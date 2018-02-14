{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DefaultSignatures #-}
module Examples.GSizeSOP where

import qualified GHC.Generics as GHC
import Generics.SOP

data Bin a = Leaf a | Bin (Bin a) (Bin a)
  deriving (Eq , Show , GHC.Generic)

instance Generic (Bin a)

class Size a where
  size :: a -> Int
  default size :: (Generic a , All2 Size (Code a))
               => a -> Int
  size = gsize

instance Size (Bin Int)
instance Size Int where
  size _ = 1

gsize :: (Generic a , All2 Size (Code a))
      => a -> Int
gsize = sum
      . hcollapse
      . hcmap (Proxy :: Proxy Size) (mapIK size)
      . from

val = Bin (Leaf (1 :: Int)) (Leaf 2)

