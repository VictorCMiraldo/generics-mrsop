{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE TypeOperators     #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE PolyKinds         #-}
-- | Standard representation of n-ary products.
module Generics.MRSOP.Base.Internal.NP where

import Generics.MRSOP.Util

infixr 5 :*
data NP :: (k -> *) -> [k] -> * where
  NP0  :: NP p '[]
  (:*) :: p x -> NP p xs -> NP p (x : xs)

instance Show (NP p '[]) where
  show NP0 = "END"
instance (Show (p x), Show (NP p xs)) => Show (NP p (x : xs)) where
  showsPrec p (v :* vs) = showParen (p > 5)
                        $ showsPrec 5 v . showString " :* " . showsPrec 5 vs

-- * Map and Elim

mapNP :: f :-> g -> NP f ks -> NP g ks
mapNP f NP0       = NP0
mapNP f (k :* ks) = f k :* mapNP f ks

elimNP :: (forall x . f x -> a) -> NP f ks -> [a]
elimNP f NP0       = []
elimNP f (k :* ks) = f k : elimNP f ks

-- * Catamorphism

cataNP :: (forall x xs . f x  -> r xs -> r (x : xs))
       -> r '[]
       -> NP f xs -> r xs
cataNP fCons fNil NP0       = fNil
cataNP fCons fNil (k :* ks) = fCons k (cataNP fCons fNil ks)

-- * Equality

eqNP :: (forall x. p x -> p x -> Bool)
     -> NP p xs -> NP p xs -> Bool
eqNP _ NP0       NP0       = True
eqNP p (x :* xs) (y :* ys) = p x y && eqNP p xs ys

