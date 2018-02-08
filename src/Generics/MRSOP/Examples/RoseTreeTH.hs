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

import Generics.MRSOP.Base.Internal.NS
import Generics.MRSOP.Base.Internal.NP
import Generics.MRSOP.Base.Universe
import Generics.MRSOP.Base.Class
import Generics.MRSOP.Konstants
import Generics.MRSOP.Util

import Generics.MRSOP.TH

import Control.Monad


-- * Haskell first-order RoseTrees

data Rose a = a :>: [Rose a ]
  deriving Show

value1, value2 :: Rose Int
value1 = 1 :>: [2 :>: [], 3 :>: []]
value2 = 1 :>: [2 :>: []]

value3 :: [Rose Int]
value3 = [value1 , value2]

value4 :: Rose Int
value4 = 12 :>: (value3 ++ value3)


deriveFamily [t| Rose Int |]

instance Eq (Rose Int) where
  (==) = geq eqSingl

correct = value1 == value1 && value1 /= value2

countEven :: Rose Int -> Int
countEven = crush countSingl sum . from' @Singl
  where
    countSingl :: Singl k -> Int
    countSingl (SInt n)
      | even n    = 1
      | otherwise = 0

