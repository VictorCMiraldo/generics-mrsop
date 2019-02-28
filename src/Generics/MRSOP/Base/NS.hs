{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
-- | Standard representation of n-ary sums.
module Generics.MRSOP.Base.NS where

import Data.Proxy
import Data.Type.Equality
import Control.Monad
import Generics.MRSOP.Util

import Unsafe.Coerce

-- |Indexed n-ary sums. This is analogous to the @Any@ datatype
--  in @Agda@. 
--  Combinations of 'Here' and 'There's are also called injections.
data NS :: (k -> *) -> [k] -> * where
  -- We'll try playing ball with the
  -- same trick as: http://hackage.haskell.org/package/freer-effects-0.3.0.1,
  -- on their definition of 'Union'
  NS :: (IsNat n) => {-# UNPACK #-} !Word -> Proxy n -> p (Lkup n xs) -> NS p xs
{-
  There :: NS p xs -> NS p (x : xs)
  Here  :: p x     -> NS p (x : xs)
-}

instance Eq1 ki => Eq1 (NS ki) where
  eq1 = eqNS eq1

-- * Map, Zip and Elim

-- |Maps over a sum
mapNS :: f :-> g -> NS f ks -> NS g ks
mapNS f (NS w p x) = NS w p (f x)

-- |Maps a monadic function over a sum
mapNSM :: (Monad m) => (forall x . f x -> m (g x)) -> NS f ks -> m (NS g ks)
mapNSM f (NS w p x) = NS w p <$> f x

-- |Eliminates a sum
elimNS :: (forall x . f x -> a) -> NS f ks -> a
elimNS f (NS w p x) = f x

-- |Combines two sums. Note that we have to fail if they are
--  constructed from different injections.
zipNS :: (MonadPlus m) => NS ki xs -> NS kj xs -> m (NS (ki :*: kj) xs)
zipNS (NS w p x) (NS z q y)
  | w == z    = return (NS w p $ x :*: unsafeCoerce y)
  | otherwise = mzero

-- * Catamorphism

{-
-- |Consumes a value of type 'NS'
cataNS :: (forall x xs . f x  -> r (x ': xs))
       -> (forall x xs . r xs -> r (x ': xs))
       -> NS f xs -> r xs
cataNS fHere fThere `(Here x)  = fHere x
cataNS fHere fThere (There x) = fThere (cataNS fHere fThere x)
-}

-- * Equality

-- |Compares two values of type 'NS' using the provided function
--  in case they are made of the same injection.
eqNS :: (forall x. p x -> p x -> Bool)
     -> NS p xs -> NS p xs -> Bool
eqNS p x = maybe False (elimNS $ uncurry' p) . zipNS x

-- * Injections

-- |A value @c :: Constr ks n@ specifies a position
--  in a type-level list. It is, in fact, isomorphic to @Fin (length ks)@.
data Constr :: [k] -> Nat -> * where
  CS :: Constr xs n -> Constr (x : xs) (S n)
  CZ ::                Constr (x : xs) Z

c2i :: (Integral i) => Constr sum n -> i
c2i CZ     = 0
c2i (CS c) = 1 + c2i c

c2Proxy :: Constr sum n -> Proxy n
c2Proxy _ = Proxy

instance TestEquality (Constr codes) where
  testEquality CZ     CZ     = Just Refl
  testEquality (CS x) (CS y) = apply (Refl :: S :~: S) <$> testEquality x y
  testEquality _      _      = Nothing

instance (IsNat n) => Show (Constr xs n) where
  show _ = "C" ++ show (getNat (Proxy :: Proxy n))

-- |We can define injections into an n-ary sum from
--  its 'Constr'uctors
injNS :: (IsNat n) => Constr sum n -> poa (Lkup n sum) -> NS poa sum
injNS c poa = NS (c2i c) (c2Proxy c) (unsafeCoerce poa)

-- | Inverse of 'injNS'.  Given some Constructor, see if Rep is of this constructor
matchNS :: Constr sum c -> NS poa sum -> Maybe (poa (Lkup c sum))
matchNS c (NS w p x)
  | c2i c == w = Just (unsafeCoerce x)
  | otherwise  = Nothing
