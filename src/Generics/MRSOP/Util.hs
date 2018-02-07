{-# LANGUAGE GADTs         #-}
{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE PolyKinds     #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes    #-}
-- |Useful utilities we need accross multiple modules.
module Generics.MRSOP.Util where

import Data.Proxy
import Data.Type.Equality
import GHC.TypeLits (TypeError , ErrorMessage(..))

-- |Natural transformations
type f :-> g = forall n . f n -> g n

-- |Type-level Peano Naturals
data Nat = S Nat | Z
  deriving (Eq , Show)

-- |Singleton Term-level natural
data SNat :: Nat -> * where
  SZ ::           SNat Z
  SS :: SNat n -> SNat (S n)

-- |And their conversion to term-level integers.
class IsNat (n :: Nat) where
  getNat  :: Proxy n -> Integer
  getSNat :: SNat n
instance IsNat Z where
  getNat p = 0
  getSNat  = SZ
instance IsNat n => IsNat (S n) where
  getNat p = 1 + getNat (unsuc p)
    where unsuc :: Proxy (S n) -> Proxy n
          unsuc _ = Proxy
  getSNat  = SS getSNat

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
