{-# LANGUAGE GADTs               #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- |Useful utilities we need accross multiple modules.
module Generics.MRSOP.Util where

import Data.Proxy
import Data.Type.Equality
import GHC.TypeLits (TypeError , ErrorMessage(..))

infixr 3 *** , &&&
(&&&) :: (a -> b) -> (a -> c) -> a -> (b , c)
f &&& g = \x -> (f x , g x)

(***) :: (a -> b) -> (c -> d) -> (a , c) -> (b , d)
f *** g = (f . fst) &&& (g . snd)

-- |Poly-kind-indexed product
data (:*:) (f :: k -> *) (g :: k -> *) (x :: k)
  = f x :*: g x

-- |Lifted curry
curry' :: ((f :*: g) x -> a) -> f x -> g x -> a
curry' f fx gx = f (fx :*: gx)

-- |Lifted uncurry
uncurry' :: (f x -> g x -> a) -> (f :*: g) x -> a
uncurry' f (fx :*: gx) = f fx gx

-- |Natural transformations
type f :-> g = forall n . f n -> g n

infixr 8 <.>
-- |Kleisli Composition
(<.>) :: (Monad m) => (b -> m c) -> (a -> m b) -> a -> m c
f <.> g = (>>= f) . g

-- |Type-level Peano Naturals
data Nat = S Nat | Z
  deriving (Eq , Show)

proxyUnsuc :: Proxy (S n) -> Proxy n
proxyUnsuc _ = Proxy

-- |Singleton Term-level natural
data SNat :: Nat -> * where
  SZ ::           SNat Z
  SS :: SNat n -> SNat (S n)

snat2int :: SNat n -> Integer
snat2int SZ     = 0
snat2int (SS n) = 1 + snat2int n

-- |And their conversion to term-level integers.
class IsNat (n :: Nat) where
  getSNat :: Proxy n -> SNat n
instance IsNat Z where
  getSNat p = SZ
instance IsNat n => IsNat (S n) where
  getSNat p = SS (getSNat $ proxyUnsuc p)

getNat :: (IsNat n) => Proxy n -> Integer
getNat = snat2int . getSNat

getSNat' :: forall (n :: Nat). IsNat n => SNat n
getSNat' = getSNat (Proxy :: Proxy n)

instance TestEquality SNat where
  testEquality SZ     SZ     = Just Refl
  testEquality (SS n) (SS m)
    = case testEquality n m of
        Nothing   -> Nothing
        Just Refl -> Just Refl
  testEquality _      _      = Nothing

-- |Type-level list lookup
type family Lkup (n :: Nat) (ks :: [k]) :: k where
  Lkup Z     (k : ks) = k
  Lkup (S n) (k : ks) = Lkup n ks
  Lkup _     '[]      = TypeError (Text "Lkup index too big")

-- |Type-level list index
type family Idx (ty :: k) (xs :: [k]) :: Nat where
  Idx x (x ': ys) = Z
  Idx x (y ': ys) = S (Idx x ys)
  Idx x '[]       = TypeError (Text "Element not found")

-- |Also list lookup, but for kind * only.
data El :: [*] -> Nat -> * where
  El :: IsNat ix => {unEl :: Lkup ix fam} -> El fam ix

-- | Convenient way to cast an 'El' index to term-level.
getElSNat :: forall ix ls. El ls ix -> SNat ix
getElSNat (El _) = getSNat' @ix

-- |Smart constructor into 'El'
into :: forall fam ty ix
      . (ix ~ Idx ty fam , Lkup ix fam ~ ty , IsNat ix)
     => ty -> El fam ix
into = El

