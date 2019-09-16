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
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

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

{-

-- |Indexed n-ary sums. This is analogous to the @Any@ datatype
--  in @Agda@. 
--  Combinations of 'Here' and 'There's are also called injections.
data NS :: (k -> *) -> [k] -> * where
  There :: NS p xs -> NS p (x : xs)
  Here  :: p x     -> NS p (x : xs)

instance EqHO phi => EqHO (NS phi) where
  eqHO = eqNS eqHO

instance EqHO phi => Eq (NS phi xs) where
  (==) = eqHO

instance ShowHO phi => ShowHO (NS phi) where
  showHO x = concat ["(" , go 0 x , ")"]
    where
      go :: ShowHO phi => Int -> NS phi xs -> String
      go n (Here r)  = "C" ++ show n ++ " " ++ showHO r
      go n (There r) = go (n+1) r

instance ShowHO phi => Show (NS phi xs) where
  show = showHO

-}

-- pattern There :: () => () => NS p xs -> NS p (x : xs)
pattern There :: forall k (a :: k -> *) (b :: [k]).
                       () =>
                       forall (xs :: [k]) (x :: k). (b ~ (x : xs)) => NS a xs -> NS a b
pattern There x = SOP.S x

-- pattern Here  :: p x     -> NS p (x : xs)
pattern Here :: forall k (a :: k -> *) (b :: [k]).
                      () =>
                      forall (x :: k) (xs :: [k]). (b ~ (x : xs)) => a x -> NS a b
pattern Here x = SOP.Z x

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

