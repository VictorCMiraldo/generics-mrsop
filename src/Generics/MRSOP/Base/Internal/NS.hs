{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE TypeOperators     #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE PolyKinds         #-}
-- | Standard representation of n-ary sums.
module Generics.MRSOP.Base.Internal.NS where

import Control.Monad
import Generics.MRSOP.Util

data NS :: (k -> *) -> [k] -> * where
  There :: NS p xs -> NS p (x : xs)
  Here  :: p x     -> NS p (x : xs)

instance Show (NS p '[]) where
  show _ = error "This code is unreachable"
instance (Show (p x), Show (NS p xs)) => Show (NS p (x : xs)) where
  show (There r) = 'T' : show r
  show (Here  x) = "H (" ++ show x ++ ")"

-- * Map and Elim

mapNS :: f :-> g -> NS f ks -> NS g ks
mapNS f (Here  p) = Here (f p)
mapNS f (There p) = There (mapNS f p)

mapMNS :: (Monad m) => (forall x . f x -> m (g x)) -> NS f ks -> m (NS g ks)
mapMNS f (Here  p) = Here  <$> f p
mapMNS f (There p) = There <$> mapMNS f p

elimNS :: (forall x . f x -> a) -> NS f ks -> a
elimNS f (Here p)  = f p
elimNS f (There p) = elimNS f p

zipNS :: (MonadPlus m) => NS k xs -> NS k xs -> m (NS (k :*: k) xs)
zipNS (Here  p) (Here  q) = return (Here (p :*: q))
zipNS (There p) (There q) = There <$> zipNS p q
zipNS _         _         = mzero

-- * Catamorphism

cataNS :: (forall x xs . f x  -> r (x ': xs))
       -> (forall x xs . r xs -> r (x ': xs))
       -> NS f xs -> r xs
cataNS fHere fThere (Here x)  = fHere x
cataNS fHere fThere (There x) = fThere (cataNS fHere fThere x)

-- * Equality

eqNS :: (forall x. p x -> p x -> Bool)
     -> NS p xs -> NS p xs -> Bool
eqNS p x = maybe False (elimNS $ uncurry' p) . zipNS x

