{-# LANGUAGE UndecidableInstances    #-}
{-# LANGUAGE RankNTypes              #-}
{-# LANGUAGE FlexibleContexts        #-}
{-# LANGUAGE FlexibleInstances       #-}
{-# LANGUAGE FlexibleInstances       #-}
{-# LANGUAGE GADTs                   #-}
{-# LANGUAGE TypeOperators           #-}
{-# LANGUAGE DataKinds               #-}
{-# LANGUAGE PolyKinds               #-}
{-# LANGUAGE ScopedTypeVariables     #-}
{-# LANGUAGE TypeApplications        #-}
{-# LANGUAGE FunctionalDependencies  #-}
module Generics.MRSOP.Base.Class where

import Data.Function (on)

import Generics.MRSOP.Base.Universe
import Generics.MRSOP.Util

-- |A type @ty@ is the @ix@-th element of a family @fam@, seen under
--  @kon@ opaque types, if we can transform back and forth
--  from a generic representation.
class Element (ki :: kon -> *) (fam :: [[[Atom kon]]]) (ix :: Nat) ty
      | ty -> fam ix
  where
    from :: ty            -> Fix ki fam ix
    to   :: Fix ki fam ix -> ty

-- |Fixing the order or arguments lets one use -XTypeApplications
--  to avoid Proxies.
from' :: forall ki fam ix ty. Element ki fam ix ty => ty -> Fix ki fam ix
from' = from
to'   :: forall ty ki fam ix. Element ki fam ix ty => Fix ki fam ix -> ty
to'   = to

-- |The most basic thing we can do is provide generic equality.
--  Our generic equality is parametrized on an equality over
--  constants, however.
geq :: (Element ki fam ix ty)
    => (forall k. ki k -> ki k -> Bool)
    -> ty -> ty -> Bool
geq kp = eqFix kp `on` from

 
