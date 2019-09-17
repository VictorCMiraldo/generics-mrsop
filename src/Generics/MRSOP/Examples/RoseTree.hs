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
{-# OPTIONS_GHC -Wno-missing-pattern-synonym-signatures #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns                #-}
{-# OPTIONS_GHC -Wno-orphans                            #-}
{-# OPTIONS_GHC -Wno-unused-top-binds                   #-}
-- |This module is analogous to 'Generics.MRSOP.Examples.RoseTreeTH',
--  but we use no Template Haskell here.
module Generics.MRSOP.Examples.RoseTree (
  -- * Non-standard Rose-Tree datatype
  -- $exp01
    R
  -- ** Family Structure
  -- $exp02
  , ListCode,RTCode,CodesRose,FamRose

  -- ** 'Family' Instance
  -- $exp03
  
  -- * Generic Combinators
  -- $exp04
  , testEq , normalize , sumTree 
  ) where

import Data.Function (on)

import Generics.MRSOP.Base
import Generics.MRSOP.Opaque


-- $exp01
--
-- Suppose we we have a mutually recursive family
-- consisting of RoseTree's with some redundant constructor:

-- | Non-standard Rose-tree datatype.
data R a = a :>: [R a]
         | Leaf a
         deriving Show

value1, value2, value3 :: R Int
value1 = 1 :>: [2 :>: [], 3 :>: []]
value2 = 1 :>: [2 :>: [] , Leaf 12]
value3 = 3 :>: [Leaf 23 , value1 , value2]


-- $exp02
--
-- The @R Int@ family has many components, that must be encoded in
-- the generics-mrsop format. These are:

-- |Codes for the @[R Int]@ type.
type ListCode = '[ '[] , '[ 'I ('S 'Z) , 'I 'Z] ]

-- |Codes for the @R Int@ type
type RTCode   = '[ '[ 'K 'KInt , 'I 'Z] , '[ 'K 'KInt] ]

-- |All codes packed in a type-level list
type CodesRose = '[ListCode , RTCode]

-- |The types corresponding the the codes in 'CodesRose'
-- appear in the same order.
type FamRose   = '[ [R Int] , R Int] 

-- ** Instance Decl

-- $exp03
--
-- Which in turn, allows us to write the 'Family' instance for
-- @R Int@. The @instance Family Singl FamRose CodesRose@ states that
-- the types in 'FamRose' follow the codes in 'CodesRose' with
-- its opaque parts represented by 'Singl' Check the source code for more details
-- on the instance.
--
-- It is worth mentioning that 'Generics.MRSOP.TH.deriveFamily' will derive
-- this code automatically.
--
-- >instance Family Singl FamRose CodesRose where
-- >   sfrom' (SS SZ) (El (a :>: as)) = Rep $ Here (NA_K (SInt a) :* NA_I (El as) :* Nil)
-- >   sfrom' (SS SZ) (El (Leaf a))   = Rep $ There (Here (NA_K (SInt a) :* Nil))
-- >   sfrom' SZ (El [])              = Rep $ Here Nil
-- >   sfrom' SZ (El (x:xs))          = Rep $ There (Here (NA_I (El x) :* NA_I (El xs) :* Nil))
-- >   sfrom' _ _ = error "unreachable"
-- > 
-- >   sto' SZ (Rep (Here Nil))
-- >     = El []
-- >   sto' SZ (Rep (There (Here (NA_I (El x) :* NA_I (El xs) :* Nil))))
-- >     = El (x : xs)
-- >   sto' (SS SZ) (Rep (Here (NA_K (SInt a) :* NA_I (El as) :* Nil)))
-- >     = El (a :>: as)
-- >   sto' (SS SZ) (Rep (There (Here (NA_K (SInt a) :* Nil))))
-- >     = El (Leaf a)
-- >   sto' _ _ = error "unreachable"


instance Family Singl FamRose CodesRose where
  sfrom' (SS SZ) (El (a :>: as)) = Rep $ Here (NA_K (SInt a) :* NA_I (El as) :* Nil)
  sfrom' (SS SZ) (El (Leaf a))   = Rep $ There (Here (NA_K (SInt a) :* Nil))
  sfrom' SZ (El [])              = Rep $ Here Nil
  sfrom' SZ (El (x:xs))          = Rep $ There (Here (NA_I (El x) :* NA_I (El xs) :* Nil))
  sfrom' _ _ = error "unreachable"

  sto' SZ (Rep (Here Nil))
    = El []
  sto' SZ (Rep (There (Here (NA_I (El x) :* NA_I (El xs) :* Nil))))
    = El (x : xs)
  sto' (SS SZ) (Rep (Here (NA_K (SInt a) :* NA_I (El as) :* Nil)))
    = El (a :>: as)
  sto' (SS SZ) (Rep (There (Here (NA_K (SInt a) :* Nil))))
    = El (Leaf a)
  sto' _ _ = error "unreachable"

instance HasDatatypeInfo Singl FamRose CodesRose where
  datatypeInfo _ SZ
    = ADT "module" (Name "[]" :@: (Name "R" :@: Name "Int"))
      $  (Constructor "[]")
      :* (Infix ":" RightAssociative 5)
      :* Nil
  datatypeInfo _ (SS SZ)
    = ADT "module" (Name "R" :@: Name "Int")
      $  (Infix ":>:" NotAssociative 0)
      :* (Constructor "Leaf")
      :* Nil
  datatypeInfo _ _
    = error "unreachable"

-- $exp04
--
-- Next, we showcase some of the simpler generic combinators provided
-- out of the box with /generics-mrsop/

instance Eq (R Int) where
  (==) = geq eqSingl `on` (into @FamRose)

-- |We can use generic equality out of the box:
--
-- > instance Eq (R Int) where
-- >   (==) = geq eqSingl `on` (into @FamRose)
--
-- If we run 'testEq' it must return @True@, naturally.
testEq :: Bool
testEq = value1 == value1
      && value2 /= value1


pattern RInt_ = SS SZ

-- |Here is an example of 'compos'; used to substitute the redundant 'Leaf'
-- constructor by its standard rose tree representation.
--
-- > normalize :: R Int -> R Int
-- > normalize = unEl . go (SS SZ) . into
-- >   where
-- >     go :: forall iy. (IsNat iy) => SNat iy -> El FamRose iy -> El FamRose iy
-- >     go (SS SZ) (El (Leaf a)) = El (a :>: []) -- (SS SZ) is the index of 'R Int' in 'CodesRose'
-- >     go _       x             = compos go x
--
-- Then, for example,
-- 
-- > normalize (42 :>: [Leaf 10 , 15 :>: [Leaf 20]]) == 42 :>: [10 :>: [] , 15 :>: [20 :>: []]]
--
normalize :: R Int -> R Int
normalize = unEl . go (SS SZ) . into
  where
    go :: forall iy. (IsNat iy) => SNat iy -> El FamRose iy -> El FamRose iy
    go RInt_ (El (Leaf a)) = El (a :>: [])
    go _       x           = compos go x

-- |Another generic combinator is 'crush'. We can 'crush' a rose tree and compute the sum
-- of all the ints stored within said tree.
--
-- > sumTree :: R Int -> Int
-- > sumTree = crush k sum . (into @FamRose)
-- >   where k :: Singl x -> Int
-- >         k (SInt n) = n
--
sumTree :: R Int -> Int
sumTree = crush k sum . (into @FamRose)
  where k :: Singl x -> Int
        k (SInt n) = n

testSum :: Bool
testSum = sumTree value3 == sumTree (normalize value3)
