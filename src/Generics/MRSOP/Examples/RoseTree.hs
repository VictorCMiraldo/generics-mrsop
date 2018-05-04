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
module Generics.MRSOP.Examples.RoseTree where

import Data.Function (on)

import Generics.MRSOP.Base
import Generics.MRSOP.Opaque
import Generics.MRSOP.Star
import Generics.MRSOP.Util

-- * Standard Rose-Tree datatype

data R a = a :>: [R a]
         | Leaf a
         deriving Show

value1, value2 :: R Int
value1 = 1 :>: [2 :>: [], 3 :>: []]
value2 = 1 :>: [2 :>: [] , Leaf 12]
value3 = 3 :>: [Leaf 23 , value1 , value2]

-- A copy of the rose tree to create other family
data R2 a = Fork2 a [R2 a]
          | Leaf2 a
          deriving Show

-- ** Family Structure

type ListCode = '[ '[] , '[I (S Z) , I Z] ]
type RTCode   = '[ '[K KInt , I Z] , '[K KInt] ]

type CodesRose = '[ListCode , RTCode]
type FamRose   = '[ [R Int] , R Int] 

-- For the copy of the rose tree
type ListCode2 = '[ '[] , '[I (S Z) , I Z] ]
type RTCode2   = '[ '[K Int , I Z] , '[K Int] ]

type CodesRose2 = '[ListCode2 , RTCode2]
type FamRose2   = '[ [R2 Int] , R2 Int] 

-- ** Instance Decl

instance Family Singl FamRose CodesRose where
  sfrom' (SS SZ) (El (a :>: as)) = Rep $ Here (NA_K (SInt a) :* NA_I (El as) :* NP0)
  sfrom' (SS SZ) (El (Leaf a))   = Rep $ There (Here (NA_K (SInt a) :* NP0))
  sfrom' SZ (El [])              = Rep $ Here NP0
  sfrom' SZ (El (x:xs))          = Rep $ There (Here (NA_I (El x) :* NA_I (El xs) :* NP0))

  sto' SZ (Rep (Here NP0))
    = El []
  sto' SZ (Rep (There (Here (NA_I (El x) :* NA_I (El xs) :* NP0))))
    = El (x : xs)
  sto' (SS SZ) (Rep (Here (NA_K (SInt a) :* NA_I (El as) :* NP0)))
    = El (a :>: as)
  sto' (SS SZ) (Rep (There (Here (NA_K (SInt a) :* NP0))))
    = El (Leaf a)

-- For the copy of the rose tree
instance Family Value FamRose2 CodesRose2 where
  sfrom' (SS SZ) (El (Fork2 a as)) = Rep $ Here (NA_K (Value a) :* NA_I (El as) :* NP0)
  sfrom' (SS SZ) (El (Leaf2 a))    = Rep $ There (Here (NA_K (Value a) :* NP0))
  sfrom' SZ (El [])                = Rep $ Here NP0
  sfrom' SZ (El (x:xs))            = Rep $ There (Here (NA_I (El x) :* NA_I (El xs) :* NP0))

  sto' SZ (Rep (Here NP0))
    = El []
  sto' SZ (Rep (There (Here (NA_I (El x) :* NA_I (El xs) :* NP0))))
    = El (x : xs)
  sto' (SS SZ) (Rep (Here (NA_K (Value a) :* NA_I (El as) :* NP0)))
    = El (Fork2 a as)
  sto' (SS SZ) (Rep (There (Here (NA_K (Value a) :* NP0))))
    = El (Leaf2 a)

instance HasDatatypeInfo Singl FamRose CodesRose Z where
  datatypeInfo _ _
    = ADT "module" (Name "[]" :@: (Name "R" :@: Name "Int"))
      $  (Constructor "[]")
      :* (Infix ":" RightAssociative 5)
      :* NP0

instance HasDatatypeInfo Singl FamRose CodesRose (S Z) where
  datatypeInfo _ _
    = ADT "module" (Name "R" :@: Name "Int")
      $  (Infix ":>:" NotAssociative 5)
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
