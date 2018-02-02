{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -cpp #-}
module TypeClassAssocFamily where

import Outline

#define Prod    [Atom]
#define Sum     [Prod]
#define Family  [Sum]

-- * Multirec

class Element ty (fam :: Family) where
  type Idx ty fam :: Nat

  from :: ty -> Fix fam (Idx ty fam)
  to   :: Fix fam (Idx ty fam) -> ty

-- * Usage

instance Element [R Int] Rose where
  type Idx [R Int] Rose = Z
  
  from []     = nil 
  from (x:xs) = cons (from x) (from xs)

  to (Fix x) = case sop x of
                    Tag CZ p -> []
                    Tag (CS CZ) (NA_I vx :* NA_I vxs :* NP0)
                       -> (to vx : to vxs)

instance Element (R Int) Rose where
  type Idx (R Int) Rose = (S Z)

  from (i :>: is) = fork i (from is)
  to (Fix (Here (NA_K i :* NA_I xs :* NP0))) = i :>: to xs
