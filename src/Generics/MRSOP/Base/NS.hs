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
  NS :: (IsNat n) => Constr' xs n -> p (Lkup n xs) -> NS p xs

instance Eq1 ki => Eq1 (NS ki) where
  eq1 = eqNS eq1

{-
  There :: NS p xs -> NS p (x : xs)
  Here  :: p x     -> NS p (x : xs)
-}

newtype Constr' (xs :: [k]) (n :: Nat)
  = Constr' { unConstr' :: Word } 

constrEq :: Constr' xs n -> Constr' xs m -> Maybe (n :~: m)
constrEq (Constr' rn) (Constr' rm)
  | rn == rm  = Just (unsafeCoerce Refl)
  | otherwise = Nothing

instance TestEquality (Constr' xs) where
  testEquality = constrEq

instance Show (Constr' xs n) where
  show (Constr' rn) = "C" ++ show rn

-- |A value @c :: Constr ks n@ specifies a position
--  in a type-level list. It is, in fact, isomorphic to @Fin (length ks)@.
data Constr :: [k] -> Nat -> * where
  CS :: Constr xs n -> Constr (x : xs) (S n)
  CZ ::                Constr (x : xs) Z

toConstr :: Constr' xs n -> Constr xs n
toConstr (Constr' 0) = unsafeCoerce CZ
toConstr (Constr' n) = unsafeCoerce (CS (toConstr (Constr' (n-1))))

fromConstr :: Constr xs n -> Constr' xs n
fromConstr = Constr' . go
  where
    go :: Constr xs n -> Word
    go CZ = 0
    go (CS c) = 1 + go c
    

instance TestEquality (Constr codes) where
  testEquality CZ     CZ     = Just Refl
  testEquality (CS x) (CS y) = apply (Refl :: S :~: S) <$> testEquality x y
  testEquality _      _      = Nothing

instance (IsNat n) => Show (Constr xs n) where
  show _ = "C" ++ show (getNat (Proxy :: Proxy n))

-- * Map, Zip and Elim

-- |Maps over a sum
mapNS :: f :-> g -> NS f ks -> NS g ks
mapNS f (NS c x) = NS c (f x)

-- |Maps a monadic function over a sum
mapNSM :: (Monad m) => (forall x . f x -> m (g x)) -> NS f ks -> m (NS g ks)
mapNSM f (NS c x) = NS c <$> f x

-- |Eliminates a sum
elimNS :: (forall x . f x -> a) -> NS f ks -> a
elimNS f (NS c x) = f x

-- |Combines two sums. Note that we have to fail if they are
--  constructed from different injections.
zipNS :: (MonadPlus m) => NS ki xs -> NS kj xs -> m (NS (ki :*: kj) xs)
zipNS (NS c x) (NS d y) = case constrEq c d of
                            Just Refl -> return (NS c $ x :*: y)
                            Nothing   -> mzero

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

{-

-}

-- |We can define injections into an n-ary sum from
--  its 'Constructors
injNS :: (IsNat n) => Constr' sum n -> poa (Lkup n sum) -> NS poa sum
injNS c poa = NS c poa

-- | Inverse of 'injNS'.  Given some Constr'uctor, see if Rep is of this constructor
matchNS :: Constr' sum c -> NS poa sum -> Maybe (poa (Lkup c sum))
matchNS c (NS d x) = case testEquality c d of
                       Just Refl -> Just x
                       Nothing   -> Nothing
