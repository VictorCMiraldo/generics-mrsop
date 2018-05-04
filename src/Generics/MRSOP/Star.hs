{-# LANGUAGE TypeInType         #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE GADTs              #-}
module Generics.MRSOP.Star where

import Data.Kind

type Star = (*)

data Value (t :: Star) :: * where
  Value :: t -> Value t