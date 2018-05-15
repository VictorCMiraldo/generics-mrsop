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
{-# LANGUAGE TemplateHaskell         #-}
{-# LANGUAGE LambdaCase              #-}
{-# LANGUAGE PatternSynonyms         #-}
-- |Usage example with template haskell support.
module Generics.MRSOP.Examples.RoseTreeTH where

{-# OPTIONS_GHC -ddump-splices #-}
import Data.Function (on)
import Data.Proxy

import Generics.MRSOP.Base
import Generics.MRSOP.Opaque
import Generics.MRSOP.Util

import Generics.MRSOP.TH

import Control.Monad


-- * Defining the datatype
--
-- $definingthedatatype
--
-- First, we will start off defining a variant of your standard Rose trees.
-- The 'Leaf' constructor adds some redundancy on purpose, so we can
-- later use the combinators in the library to remove that redundancy.

-- |Rose trees with redundancy.
data Rose a = a :>: [Rose a]
            | Leaf a
  deriving Show

-- |Sample values.
value1, value2, value3 :: Rose Int
value1 = 1 :>: [2 :>: [], 3 :>: []]
value2 = 1 :>: [2 :>: []]
value3 = 3 :>: [Leaf 23 , value1 , value2]

value4 :: Rose Int
value4 = 12 :>: [value3 , value3 , value2]

deriveFamily [t| Rose Int |]

-- * Eq Instance

-- |Equality is defined using 'geq'
instance Eq (Rose Int) where
  (==) = geq eqSingl `on` (into @FamRoseInt)

-- |Equality test; should return 'True'!
testEq :: Bool
testEq = value1 == value1
      && value2 /= value1

-- * Compos test

-- |This function removes the redundant 'Leaf' constructor
--  by the means of a 'compos'. Check the source for details.
normalize :: Rose Int -> Rose Int
normalize = unEl . go SZ . into
  where
    go :: forall iy. (IsNat iy)
       => SNat iy -> El FamRoseInt iy -> El FamRoseInt iy
    go SZ (El (Leaf a)) = El (a :>: [])
    go _  x             = compos go x

-- * Crush test

-- |Sums up the values in a rose tree using a 'crush'
sumTree :: Rose Int -> Int
sumTree = crush k sum . (into @FamRoseInt)
  where k :: Singl x -> Int
        k (SInt n) = n

-- |The sum of a tree should be the same as the sum of a normalized tree;
--  This should return 'True'.
testSum :: Bool
testSum = sumTree value3 == sumTree (normalize value3)
