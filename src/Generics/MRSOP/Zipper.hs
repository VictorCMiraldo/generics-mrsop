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
-- |Provides Zippers (aka One-hole contexts) for our
--  universe.
module Generics.MRSOP.Zipper where

import Data.Type.Equality

import Generics.MRSOP.Util hiding (Cons , Nil)
import Generics.MRSOP.Base

-- |In a @Zipper@, a Location is a a pair of a one hole context
--  and whatever was supposed to be there. In a sums of products
--  fashion, it consists of a choice of constructor and 
--  a position in the type of that constructor.
data Loc :: (kon -> *) -> [*] -> [[[Atom kon]]] -> Nat -> * where
  Loc :: IsNat ix => El fam ix -> Ctxs ki fam cs iy ix -> Loc ki fam cs iy

-- |A @Ctxs ki fam codes ix iy@ represents a value of type @El fam ix@
--  with a @El fam iy@-typed hole in it.
data Ctxs :: (kon -> *) -> [*] -> [[[Atom kon]]] -> Nat -> Nat -> * where
  Nil  :: Ctxs ki fam cs ix ix
  Cons :: (IsNat ix , IsNat a , IsNat b)
       => Ctx ki fam (Lkup ix cs) b -> Ctxs ki fam cs a ix
       -> Ctxs ki fam cs a b

-- |A @Ctx ki fam c ix@ is a choice of constructor for @c@
--  with a hole of type @ix@ inside.
data Ctx :: (kon -> *) -> [*] -> [[Atom kon]] -> Nat -> * where
  Ctx :: (IsNat n)
      => Constr c n
      -> NPHole ki fam ix (Lkup n c)
      -> Ctx ki fam c ix

-- |A @NPHole ki fam ix prod@ is a recursive position
--  of type @ix@ in @prod@.
data NPHole :: (kon -> *) -> [*] -> Nat -> [Atom kon] -> * where
  H :: PoA ki (El fam) xs -> NPHole ki fam ix (I ix : xs)
  T :: NA ki (El fam) x -> NPHole ki fam ix xs -> NPHole ki fam ix (x : xs)

-- |Existential abstraction; needed for walking the possible
--  holes in a product. We must be able to hide the type.
data NPHoleE :: (kon -> *) -> [*] -> [Atom kon] -> * where
  ExistsIX :: IsNat ix => El fam ix -> NPHole ki fam ix xs -> NPHoleE ki fam xs

-- |Given a 'PoA' (product of atoms), returns a one with a hole
--  in the first seen 'NA_I'. Note that we need the 'NPHoleE'
--  with the existential because we don't know, a priori, what
--  will be the type of such hole.
mkNPHole :: PoA ki (El fam) xs -> Maybe (NPHoleE ki fam xs)
mkNPHole NP0 = Nothing
mkNPHole (NA_I x :* xs) = Just (ExistsIX x (H xs))
mkNPHole (NA_K k :* xs)
  = do (ExistsIX el c) <- mkNPHole xs
       return (ExistsIX el (T (NA_K k) c))

-- |Given a hole and an element, put both together to form
--  the 'PoA' again.
fillNPHole :: (IsNat ix) => El fam ix -> NPHole ki fam ix xs -> PoA ki (El fam) xs
fillNPHole x (H xs)   = NA_I x :* xs
fillNPHole x (T y xs) = y :* fillNPHole x xs

-- |Given an hole and an element, return the next hole, if any.
walkNPHole :: (IsNat ix) => El fam ix -> NPHole ki fam ix xs -> Maybe (NPHoleE ki fam xs)
walkNPHole el (H xs)
  = do (ExistsIX el' c) <- mkNPHole xs
       return (ExistsIX el' (T (NA_I el) c))
walkNPHole el (T na xs)
  = do (ExistsIX el' c) <- walkNPHole el xs
       return (ExistsIX el' (T na c))

-- * Primitives

-- |Executes an action in the first hole within the given 'Rep' value,
--  if such hole can be constructed.
first :: (forall ix . IsNat ix => El fam ix -> Ctx ki fam c ix -> a)
      -> Rep ki (El fam) c -> Maybe a
first f el | Tag c p <- sop el
  = do (ExistsIX el nphole) <- mkNPHole p
       return (f el (Ctx c nphole))


-- |Fills up a hole.
fill :: (IsNat ix) => El fam ix -> Ctx ki fam c ix -> Rep ki (El fam) c
fill el (Ctx c nphole) = inj c (fillNPHole el nphole)

-- |Recursively fills a stack of holes
-- however, the Family constraint ain't so nice. so we perhaps want to
-- take zippers over a deep representation
fillCtxs :: forall ix fam iy ki c. (IsNat ix, Family ki fam c) => El fam iy -> Ctxs ki fam c ix iy -> El fam ix
-- not sure if this should be h or Nothing
fillCtxs h Nil = h
fillCtxs h (Cons ctx ctxs) =
  fillCtxs (sto @fam @ki @c $ fill h ctx) ctxs

-- |Walks to the next hole and execute an action.
next :: (IsNat ix)
     => (forall iy . IsNat iy => El fam iy -> Ctx ki fam c iy -> a)
     -> El fam ix -> Ctx ki fam c ix -> Maybe a
next f el (Ctx c nphole)
  = do (ExistsIX el' nphole') <- walkNPHole el nphole
       return (f el' (Ctx c nphole'))

-- * Navigation

-- |Move one layer deeper within the recursive structure.
down :: (Family ki fam codes , IsNat ix)
     => Loc ki fam codes ix -> Maybe (Loc ki fam codes ix)
down (Loc el ctx)
  = first (\el' ctx' -> Loc el' (Cons ctx' ctx))
          (sfrom el)

-- |Move one layer upwards within the recursive structure
up :: (Family ki fam codes, IsNat ix)
   => Loc ki fam codes ix -> Maybe (Loc ki fam codes ix)
up (Loc el Nil)             = Nothing
up (Loc el (Cons ctx ctxs)) = Just (Loc (sto $ fill el ctx) ctxs)

-- |More one hole to the right
right :: (Family ki fam codes, IsNat ix)
      => Loc ki fam codes ix -> Maybe (Loc ki fam codes ix)
right (Loc el Nil)             = Nothing
right (Loc el (Cons ctx ctxs)) = next (\el' ctx' -> Loc el' (Cons ctx' ctxs)) el ctx

-- * Interface

-- |Initializes the zipper
enter :: (Family ki fam codes , IsNat ix)
      => El fam ix -> Loc ki fam codes ix
enter el = Loc el Nil

-- |Exits the zipper
leave :: (Family ki fam codes , IsNat ix)
      => Loc ki fam codes ix -> El fam ix
leave (Loc x Nil) = x
leave loc         = maybe undefined leave $ up loc -- up returns a just!

-- |Updates the value in the hole.
update :: (Family ki fam codes , IsNat ix)
       => (forall ix . SNat ix -> El fam ix -> El fam ix)
       -> Loc ki fam codes ix -> Loc ki fam codes ix
update f (Loc el ctxs) = Loc (f (getElSNat el) el) ctxs
