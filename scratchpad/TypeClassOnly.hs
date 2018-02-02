{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -cpp #-}
module TypeClassOnly where

import Data.Proxy
import Outline

-- * Multirec

class Element (ki :: kon -> *) (fam :: [[[Atom kon]]]) (ix :: Nat) ty | ty -> fam ix where
  from :: ty -> Fix ki fam ix
  to   :: Fix ki fam ix -> ty

type HsElement = Element Singl

-- Just to fix the order of variables

from' :: forall ki fam ix ty. Element ki fam ix ty => ty -> Fix ki fam ix
from' = from
to'   :: forall ty ki fam ix. Element ki fam ix ty => Fix ki fam ix -> ty
to'   = to

from'' :: Element ki fam ix ty => Proxy ki -> Proxy fam -> Proxy ix -> ty -> Fix ki fam ix
from'' _ _ _ = from

-- * Usage

instance Element Singl Rose Z [R Int] where
  from []     = nil 
  from (x:xs) = cons (from x) (from xs)

  to (Fix x) = case sop x of
                    Tag CZ p -> []
                    Tag (CS CZ) (NA_I vx :* NA_I vxs :* NP0)
                       -> (to vx : to vxs)

instance Element Singl Rose (S Z) (R Int) where
  from (i :>: is) = fork i (from is)
  to (Fix (Here (NA_K (SInt i) :* NA_I xs :* NP0))) = i :>: to xs

value1' :: Fix Singl Rose (S Z)
value1' = from value1

value2' :: Fix Singl Rose (S Z)
value2' = from value2

eq' :: (Element ki fam ix ty)
    => (forall k. ki k -> ki k -> Bool)
    -> ty -> ty -> Bool
eq' kp x y = eqFix kp (from x) (from y)

-- * Metadata Typeclass


class (Element ki fam ix ty) => HasDatatypeInfo ki fam ix ty where
  datatypeInfo :: Proxy ki -> Proxy ty -> DatatypeInfo (Lkup ix fam)

instance HasDatatypeInfo Singl Rose (S Z) (R Int) where
  datatypeInfo pk pty = ADT "Outline" "RT"
                      $ (Infix ":>:" :* NP0)

instance HasDatatypeInfo Singl Rose Z [R Int] where
  datatypeInfo pk pty = ADT "Prelude" "[]"
                      $  (Constructor "[]")
                      :* (Infix ":")
                      :* NP0

typeset :: (forall k  . ki k -> String)
        -> (forall ix . fam ix -> String)
        -> DatatypeInfo xs -> Constr n xs -> Poa ki fam (Lkup n xs) -> String
typeset tk tf (New mn dm ci) CZ
  = typesetConstr tk tf ci
typeset tk tf (ADT mn dm (c0 :* _)) CZ
  = typesetConstr tk tf c0
typeset tk tf (ADT mn dm (_  :* cs)) (CS c)
  = typeset tk tf (ADT mn dm cs) c


typesetConstr :: (forall k  . ki k -> String)
              -> (forall ix . fam ix -> String)
              -> ConstructorInfo xs -> Poa ki fam xs
              -> String
typesetConstr tk tf (Constructor cn) poa
  = cn ++ " " ++ typesetProd tk tf poa
typesetConstr tk tf (Infix cn) (x :* y :* NP0)
  = typesetAtom tk tf x ++ " " ++ cn ++ " " ++ typesetAtom tk tf y

typesetAtom :: (forall k  . ki k -> String)
            -> (forall ix . fam ix -> String)
            -> NA ki fam k
            -> String
typesetAtom tk tf (NA_I x) = tf x
typesetAtom tk tf (NA_K k) = tk k

typesetProd :: (forall k  . ki k -> String)
            -> (forall ix . fam ix -> String)
            -> Poa ki fam xs
            -> String
typesetProd tk tf NP0 = ""
typesetProd tk tf (x :* xs) = parens (typesetAtom tk tf x) ++ maybeSpace (typesetProd tk tf xs)
  where
    parens s = '(':s ++ ")"

    maybeSpace "" = ""
    maybeSpace xs = ' ':xs

  
class HasDatatypeInfo ki fam ix ty => Pretty ki fam ix ty where
  prettyPrec :: Proxy ty -> Int -> Fix ki fam ix -> String -> String

instance Pretty Singl Rose (S Z) (R Int) where
  prettyPrec pr p (Fix r)
    = let info = datatypeInfo (Proxy :: Proxy Singl) (Proxy :: Proxy (R Int))
       in showParen (p > 10)
        ( \ss -> case sop r of
                   Tag cR pR -> typeset show _ info cR pR
        )
