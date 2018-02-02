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
-- {-# LANGUAGE AllowAmbiguousTypes #-}
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