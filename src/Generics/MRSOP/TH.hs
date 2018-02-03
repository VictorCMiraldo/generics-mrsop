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

import Control.Monad
import Language.Haskell.TH
import Language.Haskell.TH.Syntax hiding (Infix)

import qualified Data.Map as M

-- |Given the name of the first element in the family,
--  derives:
--
--    1. The other types in the family and Konstant types one needs.
--    2. the SOP code for each of the datatypes involved
--    3. One 'Element' instance per datatype
--    TODO: 4. Metadada information for each of the datatypes involved
deriveFamily :: Name -> Q [Dec]
deriveFamily name = do dec <- reifyDec name
                       main dec

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

-- Datatype info:
data DTI ty
  = ADT DataName [ CI ty ]
  | New DataName (CI ty)
  deriving (Eq , Show , Functor)

-- Constructor info is parametrised by the type of 'Types'.
-- We start by reifing declarations and producing a map of
-- (CI Type), later we translate them to (CI KorI)
data CI ty
  = Normal ConName [ty]
  | Infix  ConName ty ty
  | Record ConName [ (FieldName , ty) ]
  deriving (Eq , Show , Functor)

-- Extracts a CI from a Con
conInfo :: Con -> Q (CI Type)
conInfo (NormalC  name ty) = return $ Normal name (map snd ty)
conInfo (RecC     name ty) = return $ Record name (map (\(s , _ , t) -> (s , t)) ty)
conInfo (InfixC l name r)
  = do info <- reifyFixity name
       case info of
         _ -> return $ Infix name (snd l) (snd r)
conInfo (ForallC _ _ _) = fail "Existentials not supported"
#if MIN_VERSION_template_haskell(2,11,0)
conInfo (GadtC _ _ _)    = fail "GADTs not supported"
conInfo (RecGadtC _ _ _) = fail "GADTs not supported"
#endif

-- Extracts a DTI from a Dec
decInfo :: Dec -> Q (DTI Type)
-- decInfo (DataD    _ name (_:_) _ cons _) = fail "Parametrized types not supported" 
-- decInfo (NewtypeD _ name (_:_) _ con _)  = fail "Parametrized types not supported"
-- decInfo (TySynD     name (_:_)   ty)     = fail "Parametrized types not supported"
-- decInfo (TySynD     name []      ty)     = fail "Type Synonyms not supported"
decInfo (DataD    _ name _    _ cons _) = ADT name <$> mapM conInfo cons
decInfo (NewtypeD _ name _    _ con _)  = New name <$> conInfo con

testDec :: Q [Dec]
testDec = [d| data RoseTree = Fork Int (List RoseTree)
              data List a = Nil | Cons a (List a)    
            |]

main :: Dec -> Q [Dec]
main start
  = do
    return []
