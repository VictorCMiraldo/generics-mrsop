{-# LANGUAGE TypeApplications        #-}
{-# LANGUAGE RankNTypes              #-}
{-# LANGUAGE FlexibleContexts        #-}
{-# LANGUAGE FlexibleInstances       #-}
{-# LANGUAGE FlexibleInstances       #-}
{-# LANGUAGE GADTs                   #-}
{-# LANGUAGE TypeOperators           #-}
{-# LANGUAGE DataKinds               #-}
{-# LANGUAGE PolyKinds               #-}
{-# LANGUAGE ScopedTypeVariables     #-}
{-# LANGUAGE FunctionalDependencies  #-}
{-# LANGUAGE PatternSynonyms         #-}
-- |This module is analogous to 'Generics.MRSOP.Examples.RoseTreeTH',
--  but we use no Template Haskell here.
module Generics.MRSOP.Examples.RoseTree where

import Data.Function (on)

import Generics.MRSOP.Base
import Generics.MRSOP.Opaque
import Generics.MRSOP.Util

import Unsafe.Coerce

-- * Standard Rose-Tree datatype

data R a = a :>: [R a]
         | Leaf a
         deriving Show

value1, value2 :: R Int
value1 = 1 :>: [2 :>: [], 3 :>: []]
value2 = 1 :>: [2 :>: [] , Leaf 12]
value3 = 3 :>: [Leaf 23 , value1 , value2]

-- ** Family Structure

type ListCode = '[ '[] , '[I (S Z) , I Z] ]
type RTCode   = '[ '[K KInt , I Z] , '[K KInt] ]

type CodesRose = '[ListCode , RTCode]
type FamRose   = '[ [R Int] , R Int] 

-- ** Instance Decl


-- This example is deprecated while we work on https://github.com/VictorCMiraldo/generics-mrsop/issues/39

instance Family Singl FamRose CodesRose where
  sfrom' (SS SZ) (El (a :>: as)) = Rep $ NS (Constr' 0 :: Constr' RTCode Z)
                                            (NA_K (SInt a) :* NA_I (El as) :* NP0)
  sfrom' (SS SZ) (El (Leaf a))   = Rep $ NS (Constr' 1 :: Constr' RTCode (S Z))
                                            (NA_K (SInt a) :* NP0)
  sfrom' SZ (El [])              = Rep $ NS (Constr' 0 :: Constr' ListCode Z)
                                            NP0
  sfrom' SZ (El (x:xs))          = Rep $ NS (Constr' 1 :: Constr' ListCode (S Z))
                                            (NA_I (El x) :* NA_I (El xs) :* NP0)

  sto' SZ (Rep (NS (Constr' i) x))
    = case i of
        0 -> case x of
               NP0 -> El []
               _   -> error "malformed val"
        1 -> case x of
               (NA_I (El x) :* NA_I (El xs) :* NP0)
                 -> El (unsafeCoerce x : unsafeCoerce xs)
               _ -> error "malformed val"
  sto' (SS SZ) (Rep (NS (Constr' i) x))
    = case i of
        0 -> case x of
               (NA_K (SInt a) :* NA_I (El as) :* NP0)
                 -> El (unsafeCoerce a :>: unsafeCoerce as)
               _ -> error "malformed val"
        1 -> case x of
               (NA_K (SInt a) :* NP0)
                 -> El (Leaf (unsafeCoerce a))
               _ -> error "malfored val"

instance HasDatatypeInfo Singl FamRose CodesRose where
  datatypeInfo _ SZ
    = ADT "module" (Name "[]" :@: (Name "R" :@: Name "Int"))
      $  (Constructor "[]")
      :* (Infix ":" RightAssociative 5)
      :* NP0
  datatypeInfo _ (SS SZ)
    = ADT "module" (Name "R" :@: Name "Int")
      $  (Infix ":>:" NotAssociative 0)
      :* (Constructor "Leaf")
      :* NP0

-- * Eq Instance

instance Eq (R Int) where
  (==) = geq eqSingl `on` (into @FamRose)

testEq :: Bool
testEq = value1 == value1
      && value2 /= value1

-- * Compos test

pattern RInt_ = SS SZ

normalize :: R Int -> R Int
normalize = unEl . go (SS SZ) . into
  where
    go :: forall iy. (IsNat iy) => SNat iy -> El FamRose iy -> El FamRose iy
    go RInt_ (El (Leaf a)) = El (a :>: [])
    go _       x           = compos go x

-- * Crush test

sumTree :: R Int -> Int
sumTree = crush k sum . (into @FamRose)
  where k :: Singl x -> Int
        k (SInt n) = n

testSum :: Bool
testSum = sumTree value3 == sumTree (normalize value3)
