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
module Generics.MRSOP.TH (deriveFamily, magic) where

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

magic :: Name -> Q [Dec]
magic name = reify name >>= \res -> [d| ty = $( liftString (show res) ) |]

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

-- * Data Structures

type DataName  = Name
type ConName   = Name
type FieldName = Name
type Args      = [Name]

-- |Datatype information, parametrized by the type of Type-expressions
--  that appear on the fields of the constructors.
data DTI ty
  = ADT DataName Args [ CI ty ]
  | New DataName Args (CI ty)
  deriving (Eq , Show , Functor)

-- |Constructor information
data CI ty
  = Normal ConName [ty]
  | Infix  ConName ty ty
  | Record ConName [ (FieldName , ty) ]
  deriving (Eq , Show , Functor)

-- ** Monadic Maps

ciMapM :: (Monad m) => (ty -> m tw) -> CI ty -> m (CI tw)
ciMapM f (Normal name tys) = Normal name <$> mapM f tys
ciMapM f (Infix name l r)  = Infix name <$> f l <*> f r
ciMapM f (Record name tys) = Record name <$> mapM (rstr . (id *** f)) tys
  where
    rstr (a , b) = b >>= return . (a,)

dtiMapM :: (Monad m) => (ty -> m tw) -> DTI ty -> m (DTI tw)
dtiMapM f (ADT name args ci) = ADT name args <$> mapM (ciMapM f) ci
dtiMapM f (New name args ci) = New name args <$> ciMapM f ci

-- * Simpler STy Language

-- A Simplified version of Language.Haskell.TH
data STy
  = AppST STy STy
  | VarST Name
  | ConST Name
  deriving (Eq , Show, Ord)

-- ** Back and Forth conversion

convertType :: (Monad m) => Type -> m STy
convertType (AppT a b)  = AppST <$> convertType a <*> convertType b
convertType (SigT t _)  = convertType t
convertType (VarT n)    = return (VarST n)
convertType (ConT n)    = return (ConST n)
convertType (ParensT t) = convertType t
convertType _           = fail "convertType: Unsupported Type"

trevnocType :: STy -> Type
trevnocType (AppST a b) = AppT (trevnocType a) (trevnocType b)
trevnocType (VarST n)   = VarT n
trevnocType (ConST n)   = ConT n

-- |Handy substitution function.
--
--  @stySubst t m n@ substitutes m for n within t, that is: t[m/n]
stySubst :: STy -> Name -> STy -> STy
stySubst (AppST a b) m n = AppST (stySubst a m n) (stySubst b m n)
stySubst (ConST a)   m n = ConST a
stySubst (VarST x)   m n
  | x == m    = n
  | otherwise = VarST x

-- * Monad
--
-- Keeks the (M.Map STy (Int , DTI Sty)) in a state.

data Idxs 
  = Idxs { idxsNext :: Int
         , idxsMap  :: M.Map STy (Int , Maybe (DTI STy))
         }

onMap :: (M.Map STy (Int , Maybe (DTI STy)) -> M.Map STy (Int , Maybe (DTI STy)))
      -> Idxs -> Idxs
onMap f (Idxs n m) = Idxs n (f m)

type IdxsM = StateT Idxs

runIdxsM :: (Monad m) => IdxsM m a -> m a
runIdxsM = flip evalStateT (Idxs 0 M.empty)

-- |The actual monad we need to run all of this;
type M = IdxsM Q

-- |Returns the index of a "Name" within the family.
--  If this name has not been registered yet, returns
--  a fresh index.
indexOf :: (Monad m) => STy -> IdxsM m Int
indexOf name
  = do st <- get
       case M.lookup name (idxsMap st) of
         Just i  -> return (fst i)
         Nothing -> let i = idxsNext st
                     in put (Idxs (i + 1) (M.insert name (i , Nothing) (idxsMap st)))
                     >> return i

-- |Register some Datatype Information for a given STy
register :: (Monad m) => STy -> DTI STy -> IdxsM m ()
register ty info = indexOf ty -- the call to indexOf guarantees the
                              -- adjust will do something;
                >> modify (onMap $ M.adjust (id *** const (Just info)) ty) 

-- |A more rigorous follow up of our sketch up there.
process :: STy -> M ()
process ty
  = do ix <- indexOf ty
       _



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

-- We shall need to keep track of the indexes of the types
-- we explore.

-- Now, we start processing by extracting a (DTI STy) from
-- a Haskell Declaration.

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



main :: Dec -> Q [Dec]
main start
  = do
    return []
