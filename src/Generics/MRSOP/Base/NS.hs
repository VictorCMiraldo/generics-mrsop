{-# LANGUAGE PatternSynonyms             #-}
{-# LANGUAGE RankNTypes                  #-}
{-# LANGUAGE FlexibleContexts            #-}
{-# LANGUAGE FlexibleInstances           #-}
{-# LANGUAGE GADTs                       #-}
{-# LANGUAGE TypeOperators               #-}
{-# LANGUAGE DataKinds                   #-}
{-# LANGUAGE PolyKinds                   #-}
{-# LANGUAGE ScopedTypeVariables         #-}
{-# LANGUAGE ScopedTypeVariables         #-}
{-# OPTIONS_GHC -Wno-name-shadowing      #-}
{-# OPTIONS_GHC -Wno-orphans             #-}

-- | Standard representation of n-ary sums.
module Generics.MRSOP.Base.NS
  ( SOP.NS , pattern Here , pattern There
  , mapNS
  , mapNSM
  , elimNS 
  , zipNS
  , cataNS
  , eqNS
  ) where

import qualified Data.SOP.NS as SOP
import           Data.SOP.NS (NS(..))

import Control.Monad
import Generics.MRSOP.Util

-- |Pattern synonym to 'SOP.S'
pattern There :: forall k (a :: k -> *) (b :: [k]). ()
              => forall (xs :: [k]) (x :: k). (b ~ (x : xs))
              => NS a xs -> NS a b
pattern There x = SOP.S x

-- |Pattern synonym to 'SOP.Z'
pattern Here :: forall k (a :: k -> *) (b :: [k]). ()
             => forall (x :: k) (xs :: [k]). (b ~ (x : xs))
             => a x -> NS a b
pattern Here x = SOP.Z x

{-# COMPLETE Here, There #-}

-- |@since 2.3.0
instance EqHO f => EqHO (NS f) where
  eqHO (Here fx) (Here fy) = eqHO fx fy
  eqHO (There x) (There y) = eqHO x y
  eqHO _         _         = False

-- |@since 2.3.0
instance ShowHO f => ShowHO (NS f) where
  showsPrecHO d (Here fx) = showParen (d > app_prec) $
    showString "Here " . showsPrecHO (app_prec+1) fx
   where app_prec = 10
  showsPrecHO d (There fx) = showParen (d > app_prec) $
    showString "There " . showsPrecHO (app_prec+1) fx
   where app_prec = 10

-- * Map, Zip and Elim

-- |Maps over a sum
mapNS :: f :-> g -> NS f ks -> NS g ks
mapNS f (Here  p) = Here (f p)
mapNS f (There p) = There (mapNS f p)

-- |Maps a monadic function over a sum
mapNSM :: (Monad m) => (forall x . f x -> m (g x)) -> NS f ks -> m (NS g ks)
mapNSM f (Here  p) = Here  <$> f p
mapNSM f (There p) = There <$> mapNSM f p

-- |Eliminates a sum
elimNS :: (forall x . f x -> a) -> NS f ks -> a
elimNS f (Here p)  = f p
elimNS f (There p) = elimNS f p

-- |Combines two sums. Note that we have to fail if they are
--  constructed from different injections.
zipNS :: (MonadPlus m) => NS ki xs -> NS kj xs -> m (NS (ki :*: kj) xs)
zipNS (Here  p) (Here  q) = return (Here (p :*: q))
zipNS (There p) (There q) = There <$> zipNS p q
zipNS _         _         = mzero

-- * Catamorphism

-- |Consumes a value of type 'NS'
cataNS :: (forall x xs . f x  -> r (x ': xs))
       -> (forall x xs . r xs -> r (x ': xs))
       -> NS f xs -> r xs
cataNS fHere _fThere (Here x)  = fHere x
cataNS fHere fThere  (There x) = fThere (cataNS fHere fThere x)

-- * Equality

-- |Compares two values of type 'NS' using the provided function
--  in case they are made of the same injection.
eqNS :: (forall x. p x -> p x -> Bool)
     -> NS p xs -> NS p xs -> Bool
eqNS p x = maybe False (elimNS $ uncurry' p) . zipNS x

