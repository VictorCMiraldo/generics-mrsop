{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -cpp #-}
module TypeClassOnly where

import Outline

#define Prod    [Atom]
#define Sum     [Prod]
#define Family  [Sum]

-- * Multirec

class Element ty (fam :: Family) (ix :: Nat) {- | ty -> fam ix -} where
  from :: ty -> Fix fam ix
  to   :: Fix fam ix -> ty

-- Just to fix the order of variables

from' :: forall fam ix ty. Element ty fam ix => ty -> Fix fam ix
from' = from
to'   :: forall ty fam ix. Element ty fam ix => Fix fam ix -> ty
to'   = to

-- * Usage

instance Element [R Int] Rose Z where
  from []     = nil 
  from (x:xs) = cons (from x) (from xs)

  to (Fix x) = case sop x of
                    Tag CZ p -> []
                    Tag (CS CZ) (NA_I vx :* NA_I vxs :* NP0)
                       -> (to vx : to vxs)

instance Element (R Int) Rose (S Z) where
  from (i :>: is) = fork i (from is)
  to (Fix (Here (NA_K i :* NA_I xs :* NP0))) = i :>: to xs

value1 :: Fix Rose (S Z)
value1 = from value

-- Using TypeApplications
value2 = from' @Rose @(S Z) value