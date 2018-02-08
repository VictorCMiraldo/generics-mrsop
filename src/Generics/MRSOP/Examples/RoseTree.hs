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
module Generics.MRSOP.Examples.RoseTree where

import Data.Function (on)

import Generics.MRSOP.Base.Internal.NS
import Generics.MRSOP.Base.Internal.NP
import Generics.MRSOP.Base.Universe
import Generics.MRSOP.Base.Class
import Generics.MRSOP.Konstants
import Generics.MRSOP.Util


-- * Haskell first-order RoseTrees

data RoseTree = Int :>: [RoseTree]
  deriving Show

value1, value2 :: RoseTree
value1 = 1 :>: [2 :>: [], 3 :>: []]
value2 = 1 :>: [2 :>: []]

-- * Generic SOP RoseTrees

-- Sum-of-products of both the List and RoseTree types
type ListS     = '[ '[] , '[I (S Z) , I Z] ]
type RoseTreeS = '[ '[K KInt , I Z] ]
type RoseFam   = '[ ListS , RoseTreeS ]

type GRoseTree = Fix Singl RoseFam (S Z)
type GList     = Fix Singl RoseFam Z

nil :: GList
nil = Fix $ Rep (Here NP0)

cons :: GRoseTree -> GList -> GList
cons x xs = Fix $ Rep (There $ Here (NA_I x :* NA_I xs :* NP0))

fork :: Int -> GList -> GRoseTree
fork x xs = Fix $ Rep (Here (NA_K (SInt x) :* NA_I xs :* NP0))

-- ** Proof of membership
--
-- GRoseTree and GList belong in the family.

instance Element Singl RoseFam Z [RoseTree] where
  from []     = nil 
  from (x:xs) = cons (from x) (from xs)

  to (Fix x) = case sop x of
                    Tag CZ p -> []
                    Tag (CS CZ) (NA_I vx :* NA_I vxs :* NP0)
                       -> (to vx : to vxs)

instance Element Singl RoseFam (S Z) RoseTree where
  from (i :>: is) = fork i (from is)
  to (Fix (Rep (Here (NA_K (SInt i) :* NA_I xs :* NP0))))
    = i :>: to xs

-- * Eq instance

instance Eq RoseTree where
  (==) = geq eqSingl

correct :: Bool
correct = value1 == value1
       && value2 /= value1
