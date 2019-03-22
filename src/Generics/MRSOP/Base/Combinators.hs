{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
-- | A collection of combinators
--   for operating over sums of products.
module Generics.MRSOP.Base.Combinators where

import Data.Function (on)

import Control.Monad.Identity

import Generics.MRSOP.Base.Universe    
import Generics.MRSOP.Base.Class       
import Generics.MRSOP.Util

-- * Equality
--
-- $equality
--
-- Compares two elements for equality.

-- |Given a way to compare the constant types
--  within two values, compare the outer values for
--  syntatical equality.
geq :: forall ki fam codes ix
     . (Family ki fam codes)
    => (forall k . ki k -> ki k -> Bool)
    -> El fam ix -> El fam ix -> Bool
geq kp = eqFix kp `on` dfrom 

-- * Compos
--
-- $compos
--
-- Applies a morphism everywhere in a structure.
--
-- Conceptually one can think of 'compos' as
-- having type @(b -> b) -> a -> a@. The semantics
-- is applying the morphism over @b@s wherever possible
-- inside a value of type @a@.
--
-- For our case, we need @a@ and @b@ to be elements of
-- the same family.

-- |Given a morphism for the @iy@ element of the family,
--  applies it everywhere in another element of
--  the family.
composM :: forall ki fam codes ix m
         . (Monad m , Family ki fam codes, IsNat ix)
        => (forall iy . IsNat iy => SNat iy -> El fam iy -> m (El fam iy))
        -> El fam ix -> m (El fam ix)
composM f = (sto @fam <$>)
          . mapRepM (\x -> f (getElSNat x) x)
          . sfrom @fam

-- |Non monadic version from above.
compos :: forall ki fam codes ix
        . (Family ki fam codes, IsNat ix)
       => (forall iy . IsNat iy => SNat iy -> El fam iy -> El fam iy)
       -> El fam ix -> El fam ix
compos f = runIdentity . composM (\iy -> return . f iy)

-- * Crush
--
-- $crush
--
-- Crush will collapse an entire value given only
-- an action to perform on the leaves and a way
-- of combining results.

-- | 'crushM' Applies its first parameter to all leaves,
--   combines the results with its second parameter.
crushM :: forall ki fam codes ix r m
        . (Monad m , Family ki fam codes)
       => (forall k. ki k -> m r) -> ([r] -> m r)
       -> El fam ix -> m r
crushM kstep combine
  = elimRep kstep (crushM kstep combine) (combine <.> sequence) . sfrom

-- | Non-monadic version
crush :: forall ki fam codes ix r
       . (Family ki fam codes)
      => (forall k. ki k -> r) -> ([r] -> r)
      -> El fam ix -> r
crush kstep combine = runIdentity . crushM (return . kstep) (return . combine)
