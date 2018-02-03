{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveTraversable #-}
{-# OPTIONS_GHC -cpp         #-}
{-# LANGUAGE DeriveFunctor   #-}
{-# LANGUAGE TemplateHaskell #-}
-- | Provides a simple way for the end-user deriving
--   the mechanical, yet long, Element instances
--   for a family.
--
--   We are borrowing a lot of code from generic-sop
--   ( https://hackage.haskell.org/package/generics-sop-0.3.2.0/docs/src/Generics-SOP-TH.html )
--
module Generics.MRSOP.TH (deriveFamily) where

import Control.Arrow ((***))
import Control.Monad
import Control.Monad.State
import Control.Monad.Identity

import Language.Haskell.TH
import Language.Haskell.TH.Syntax (liftString)


import qualified Data.Map as M

-- |Given the name of the first element in the family,
--  derives:
--
--    1. The other types in the family and Konstant types one needs.
--    2. the SOP code for each of the datatypes involved
--    3. One 'Element' instance per datatype
--    TODO: 4. Metadada information for each of the datatypes involved
deriveFamily :: Q Type -> Q [Dec]
deriveFamily t
  = do res <- t
       [d| ty :: String
           ty = $( liftString (show res) ) |]

-- Sketch;
--
--   Given a module:
--
--    > module Test where
--    > data Rose a = Fork a [Rose a]
--    > $(deriveFamily [t| Rose Int |])
--
--  We will see we are looking into deriving a family
--  for an AppT (ConT Rose) (ConT Int).
--
--  Working with a (M.Map STy (Int , DInfo (K + I))) in a state;
--
--  0) Translate to a simpler Type-expression, call it STy.
--  1) Register (AppST (ConST Rose) (ConST Int)) as family index Z
--  2) reify lhs: [d| data Rose a = Fork a [Rose a] |]
--      a) reduce rhs of (1): (\a -> Fork a [Rose a]) @ (ConT Int)
--                        == Fork Int [Rose Int]
--      b) Take the fields that require processing: [ConT Int , AppST List (AppST Rose Int)]
--      c) Somehow figure out that (ConT Int) is a Konstant.
--      d) Look into (AppST List (AppST Rose Int))
--      e) Is it already processed?
--      f) If yes, we are done.
--  3) Register (AppST List (AppST Rose Int))as family index (S Z)
--  4) reify lhs: [d| data List a = Nil | Cons a (List a) |]
--      a) reduce rhs of (4): (\a -> Nil | Cons a (List a)) @ (AppST Rose Int)
--      b) Take the fields of each constructor:
--           [] , [AppST Rose Int , AppST List (AppST Rose Int)]
--      c) Notice that both fields of 'Cons' have already
--         been registered; hence they become: [I Z , I (S Z)]
--

-- OLD COLD CODE:

---------------
-- Internals --
---------------

-- Utils

reifyDec :: Name -> Q Dec
reifyDec name =
  do info <- reify name
     case info of TyConI dec -> return dec
                  _          -> fail "Info must be type declaration type."

-- Our data structure

type DataName  = Name
type ConName   = Name
type FieldName = Name
type Args      = [Name]

-- Datatype info:
data DTI ty
  = ADT DataName Args [ CI ty ]
  | New DataName Args (CI ty)
  deriving (Eq , Show , Functor)

-- Constructor info is parametrised by the type of 'Types'.
-- We start by reifing declarations and producing a map of
-- (CI Type), later we translate them to (CI KorI)
data CI ty
  = Normal ConName [ty]
  | Infix  ConName ty ty
  | Record ConName [ (FieldName , ty) ]
  deriving (Eq , Show , Functor)

ciMapM :: (Monad m) => (ty -> m tw) -> CI ty -> m (CI tw)
ciMapM f (Normal name tys) = Normal name <$> mapM f tys
ciMapM f (Infix name l r)  = Infix name <$> f l <*> f r
ciMapM f (Record name tys) = Record name <$> mapM (rstr . (id *** f)) tys
  where
    rstr (a , b) = b >>= return . (a,)

dtiMapM :: (Monad m) => (ty -> m tw) -> DTI ty -> m (DTI tw)
dtiMapM f (ADT name args ci) = ADT name args <$> mapM (ciMapM f) ci
dtiMapM f (New name args ci) = New name args <$> ciMapM f ci

-- A Simplified version of Language.Haskell.TH
data STy
  = AppST STy STy
  | VarST Name
  | ConST Name
  | KonST Name
  deriving (Eq , Show, Ord)

-- We shall need to keep track of the indexes of the types
-- we explore.

data Idxs idx
  = Idxs { idxsNext :: Int
         , idxsMap  :: M.Map idx (Int , Maybe (DTI STy))
         }

type IdxsM idx = StateT (Idxs idx)

-- |The actual monad we need to run all of this;
type M = IdxsM STy Q

-- |Returns the index of a "Name" within the family.
--  If this name has not been registered yet, returns
--  a fresh index.
indexOf :: (Ord idx, Monad m) => idx -> IdxsM idx m Int
indexOf name
  = do st <- get
       case M.lookup name (idxsMap st) of
         Just i  -> return (fst i)
         Nothing -> let i = idxsNext st
                     in put (Idxs (i + 1) (M.insert name (i , Nothing) (idxsMap st)))
                     >> return i

-- Now, we start processing by extracting a (DTI STy) from
-- a Haskell Declaration.

convertType :: Type -> M STy
convertType (AppT a b)  = AppST <$> convertType a <*> convertType b
convertType (SigT t _)  = convertType t
convertType (VarT n)    = return (VarST n)
convertType (ConT n)    = return (ConST n)
convertType (ParensT t) = convertType t
convertType _           = fail "convertType: Unsupported Type"

argInfo :: TyVarBndr -> Name
argInfo (PlainTV  n)   = n
argInfo (KindedTV n _) = n

-- Extracts a DTI from a Dec
decInfo :: Dec -> M (DTI Type)
decInfo (TySynD     name args      ty)     = fail "Type Synonyms not supported"
decInfo (DataD    _ name args    _ cons _) = ADT name (map argInfo args) <$> mapM conInfo cons
decInfo (NewtypeD _ name args    _ con _)  = New name (map argInfo args) <$> conInfo con
decInfo _                                  = fail "Only type declarations are supported"


-- Extracts a CI from a Con
conInfo :: Con -> M (CI Type)
conInfo (NormalC  name ty) = return $ Normal name (map snd ty)
conInfo (RecC     name ty) = return $ Record name (map (\(s , _ , t) -> (s , t)) ty)
conInfo (InfixC l name r)
  = do info <- lift (reifyFixity name)
       case info of
         -- TODO: incorporate fixity information.
         _ -> return $ Infix name (snd l) (snd r)
conInfo (ForallC _ _ _) = fail "Existentials not supported"
#if MIN_VERSION_template_haskell(2,11,0)
conInfo (GadtC _ _ _)    = fail "GADTs not supported"
conInfo (RecGadtC _ _ _) = fail "GADTs not supported"
#endif

testDec :: Q [Dec]
testDec = [d| data RoseTree = Fork Int (List RoseTree)
              data List a = Nil | Cons a (List a)    
            |]


runIdxsM :: (Ord idx, Monad m) => IdxsM idx m a -> m a
runIdxsM = flip evalStateT (Idxs 0 M.empty)

main :: Dec -> Q [Dec]
main start
  = do
    return []
