{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DefaultSignatures #-}
module Examples.GSizeGenerics where

import GHC.Generics

data Bin a = Leaf a | Bin (Bin a) (Bin a)
  deriving (Eq , Show , Generic)

class Size (a :: *) where
  size :: a -> Int
  default size  :: (Generic a , GSize (Rep a))
                => a -> Int
  size = gsize . from

class GSize (pf :: * -> *) where
  gsize :: pf x -> Int

instance GSize V1 where gsize _ = 0

instance GSize U1 where gsize _ = 1

instance (GSize f , GSize g) => GSize (f :*: g) where
  gsize (f :*: g) = gsize f + gsize g

instance (GSize f , GSize g) => GSize (f :+: g) where
  gsize (L1 f) = gsize f
  gsize (R1 g) = gsize g

instance (Size a) => GSize (K1 R a) where
  gsize (K1 a) = size a

instance (GSize f) => GSize (M1 s i f) where
  gsize (M1 a) = gsize a

instance Size (Bin Int)

instance Size Int where
  size _ = 1

val = Bin (Leaf (1 :: Int)) (Leaf 2)
