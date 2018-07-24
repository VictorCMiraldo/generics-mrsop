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
-- | Provides one-hole contexts for our universe, but over
--   deep encoded datatypes. These are a bit easier to use
--   computationally.
--
--   This module follows the very same structure as 'Generics.MRSOP.Zipper'.
--   Refer there for further documentation.
module Generics.MRSOP.Zipper.Deep where
import Control.Monad (guard)
import Data.Proxy

import Generics.MRSOP.Util hiding (Cons , Nil)
import Generics.MRSOP.Base

-- |Analogous to 'Generics.MRSOP.Zipper.Ctxs'
data Ctxs (ki :: kon -> *) (codes :: [[[Atom kon]]]) :: Nat -> Nat -> * where
  Nil :: Ctxs ki codes ix ix
  Cons
    :: (IsNat ix, IsNat a, IsNat b)
    => Ctx ki codes (Lkup ix codes) b
    -> Ctxs ki codes a ix
    -> Ctxs ki codes a b

-- |Analogous to 'Generics.MRSOP.Zipper.Ctx'
data Ctx (ki :: kon -> *) (codes :: [[[Atom kon]]]) :: [[Atom kon]] -> Nat -> * where
  Ctx
    :: Constr c n -> NPHole ki codes ix (Lkup n c) -> Ctx ki codes c ix

-- |Analogous to 'Generics.MRSOP.Zipper.NPHole', but uses a deep representation
--  for generic values.
data NPHole (ki :: kon -> *) (codes :: [[[Atom kon]]]) :: Nat -> [Atom kon] -> * where
  H :: PoA ki (Fix ki codes) xs -> NPHole ki codes ix ('I ix ': xs)
  T
    :: NA ki (Fix ki codes) x
    -> NPHole ki codes ix xs
    -> NPHole ki codes ix (x ': xs)

getCtxsIx :: Ctxs ki codes iy ix -> Proxy ix
getCtxsIx _ = Proxy

-- | Given a product with a hole in it, and an element, get back
-- a product
--
-- dual of 'removeNPHole'
fillNPHole ::
     IsNat ix
  => Fix ki codes ix
  -> NPHole ki codes ix xs
  -> PoA ki (Fix ki codes) xs
fillNPHole x (H xs) = NA_I x :* xs
fillNPHole x (T y ys) = y :* fillNPHole x ys

-- |Given a value that fits in a context, fills the context hole.
fillCtxs ::
     (IsNat ix) => Fix ki codes iy -> Ctxs ki codes ix iy -> Fix ki codes ix
fillCtxs h Nil = h
fillCtxs h (Cons ctx ctxs) = fillCtxs (Fix $ fillCtx h ctx) ctxs

fillCtx ::
     (IsNat ix)
  => Fix ki codes ix
  -> Ctx ki codes c ix
  -> Rep ki (Fix ki codes) c
fillCtx x (Ctx c nphole) = inj c (fillNPHole x nphole)

-- |Given a value and a context, tries to match to context
-- in the value and, upon success, returns whatever overlaps with
-- the hole.
removeCtxs ::
     (Eq1 ki, IsNat ix)
  => Ctxs ki codes ix iy
  -> Fix ki codes ix
  -> Maybe (Fix ki codes iy)
removeCtxs Nil f = pure f
removeCtxs (Cons ctx ctxs) (Fix r) = do
    (Fix t) <- removeCtxs ctxs (Fix r)
    removeCtx t ctx
  
removeCtx :: forall ix ki codes c.
     (Eq1 ki, IsNat ix)
  => Rep ki (Fix ki codes) c
  -> Ctx ki codes c ix
  -> Maybe (Fix ki codes ix)
removeCtx x (Ctx c npHole) =
  match c x >>= removeNPHole npHole

removeNPHole ::
     (Eq1 ki, IsNat ix)
  => NPHole ki codes ix xs
  -> PoA ki (Fix ki codes) xs
  -> Maybe (Fix ki codes ix)
removeNPHole (H ys) (NA_I x :* xs) = do
  guard $ eq1 xs ys
  pure x
removeNPHole (T y ys) (x :* xs) = do
  guard $ eq1 x y
  removeNPHole ys xs
