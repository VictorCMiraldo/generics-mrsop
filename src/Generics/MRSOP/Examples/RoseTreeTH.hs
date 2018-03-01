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
module Generics.MRSOP.Examples.RoseTreeTH where

{-# OPTIONS_GHC -ddump-splices #-}
import Data.Function (on)
import Data.Proxy

import Generics.MRSOP.Base
import Generics.MRSOP.Opaque
import Generics.MRSOP.Util

import Generics.MRSOP.TH

import Control.Monad


-- * Haskell first-order RoseTrees

data Rose a = a :>: [Rose a]
            | Leaf a
  deriving Show

value1, value2, value3 :: Rose Int
value1 = 1 :>: [2 :>: [], 3 :>: []]
value2 = 1 :>: [2 :>: []]
value3 = 3 :>: [Leaf 23 , value1 , value2]

value4 :: Rose Int
value4 = 12 :>: [value3 , value3 , value2]

deriveFamily [t| Rose Int |]

-- * Eq Instance

instance Eq (Rose Int) where
  (==) = geq eqSingl `on` (into @FamRoseInt)

testEq :: Bool
testEq = value1 == value1
      && value2 /= value1

-- * Compos test

normalize :: Rose Int -> Rose Int
normalize = unEl . go SZ . into
  where
    go :: forall iy. (IsNat iy)
       => SNat iy -> El FamRoseInt iy -> El FamRoseInt iy
    go SZ (El (Leaf a)) = El (a :>: [])
    go _  x             = compos go x

-- * Crush test

sumTree :: Rose Int -> Int
sumTree = crush k sum . (into @FamRoseInt)
  where k :: Singl x -> Int
        k (SInt n) = n

testSum :: Bool
testSum = sumTree value3 == sumTree (normalize value3)

pf :: Proxy FamRoseInt
pf = Proxy

pr :: Proxy [ Rose Int ]
pr = Proxy
