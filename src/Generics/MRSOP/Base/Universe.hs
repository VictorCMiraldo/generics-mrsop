{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE ScopedTypeVariables  #-}
-- | Our universe representation
module Generics.MRSOP.Base.Universe where

import Data.Function (on)
import Data.Type.Equality
import Data.Proxy

import Control.Monad

import Generics.MRSOP.Base.NS
import Generics.MRSOP.Base.NP
import Generics.MRSOP.Util

-- * Universe of Codes
--
-- We will use nested lists to represent the Sums-of-Products
-- structure. The atoms, however, will be parametrized by a kind
-- used to index what are the types that are opaque to the library.
--

-- |Atoms can be either opaque types or
--  type variables.
data Atom kon
  = K kon
  | I Nat
  deriving (Eq, Show)

-- |@NA ki phi a@ provides an interpretation for an atom @a@,
--  using either @ki@ or @phi@ to interpret the type variable
--  or opaque type.
data NA  :: (kon -> *) -> (Nat -> *) -> Atom kon -> * where
  NA_I :: (IsNat k) => phi k -> NA ki phi (I k) 
  NA_K ::              ki  k -> NA ki phi (K k)

-- ** Map, Elim and Zip

-- |Maps a natural transformation over an atom interpretation
mapNA :: (forall k  .             ki k  -> kj k)
      -> (forall ix . IsNat ix => f  ix -> g  ix)
      -> NA ki f a -> NA kj g a
mapNA fk fi (NA_I f) = NA_I (fi f)
mapNA fk fi (NA_K k) = NA_K (fk k)

-- |Maps a monadic natural transformation over an atom interpretation
mapMNA :: (Monad m)
       => (forall k  .             ki k  -> m (kj k))
       -> (forall ix . IsNat ix => f  ix -> m (g  ix))
       -> NA ki f a -> m (NA kj g a)
mapMNA fk fi (NA_K k) = NA_K <$> fk k
mapMNA fk fi (NA_I f) = NA_I <$> fi f

-- |Eliminates an atom interpretation
elimNA :: (forall k . ki  k -> b)
       -> (forall k . phi k -> b)
       -> NA ki phi a -> b
elimNA kp fp (NA_I x) = fp x
elimNA kp fp (NA_K x) = kp x

-- |Combines two atoms into one
zipNA :: NA ki f a -> NA kj g a -> NA (ki :*: kj) (f :*: g) a
zipNA (NA_I fk) (NA_I gk) = NA_I (fk :*: gk)
zipNA (NA_K ki) (NA_K kj) = NA_K (ki :*: kj)

-- |Compares atoms provided we know how to compare
--  the leaves, both recursive and constant.
eqNA :: (forall k  . ki  k  -> ki  k  -> Bool)
     -> (forall ix . fam ix -> fam ix -> Bool)
     -> NA ki fam l -> NA ki fam l -> Bool
eqNA kp fp x = elimNA (uncurry' kp) (uncurry' fp) . zipNA x

-- * Representation of Codes
--
-- Codes are represented using the 'Rep' newtype,
-- which wraps an n-ary sum of n-ary products. 

-- |Representation of codes.
newtype Rep (ki :: kon -> *) (phi :: Nat -> *) (code :: [[Atom kon]])
  = Rep { unRep :: NS (PoA ki phi) code }

-- |Product of Atoms is a handy synonym to have.
type PoA (ki :: kon -> *) (phi :: Nat -> *) = NP (NA ki phi)

-- ** Map, Elim and Zip
--
-- Just like for 'NS', 'NP' and 'NA', we provide
-- a couple convenient functions working over
-- a 'Rep'. These are just the cannonical combination
-- of their homonym versions in 'NS', 'NP' or 'NA'.

mapRep :: (forall ix . IsNat ix => f  ix -> g ix)
       -> Rep ki f c -> Rep ki g c
mapRep = hmapRep id

mapMRep :: (Monad m)
        => (forall ix . IsNat ix => f  ix -> m (g  ix))
        -> Rep ki f c -> m (Rep ki g c)
mapMRep = hmapMRep return

hmapRep :: (forall k  .             ki k  -> kj k)
        -> (forall ix . IsNat ix => f  ix -> g ix)
        -> Rep ki f c -> Rep kj g c
hmapRep fk fi = Rep . mapNS (mapNP (mapNA fk fi)) . unRep

hmapMRep :: (Monad m)
         => (forall k  .             ki k  -> m (kj k))
         -> (forall ix . IsNat ix => f  ix -> m (g  ix))
         -> Rep ki f c -> m (Rep kj g c)
hmapMRep fk fi = (Rep <$>) . mapMNS (mapMNP (mapMNA fk fi)) . unRep

zipRep :: (MonadPlus m)
       => Rep ki f c -> Rep kj g c
       -> m (Rep (ki :*: kj) (f :*: g) c)
zipRep (Rep t) (Rep u)
  = Rep . mapNS (mapNP (uncurry' zipNA) . uncurry' zipNP) <$> zipNS t u

elimRep :: (forall k . ki k -> a)
        -> (forall k . f  k -> a)
        -> ([a] -> b)
        -> Rep ki f c -> b
elimRep kp fp cat = elimNS (cat . elimNP (elimNA kp fp)) . unRep

eqRep :: (forall k  . ki  k  -> ki  k  -> Bool)
      -> (forall ix . fam ix -> fam ix -> Bool)
      -> Rep ki fam c -> Rep ki fam c -> Bool
eqRep kp fp t = maybe False (elimRep (uncurry' kp) (uncurry' fp) and)
              . zipRep t 

-- * SOP functionality
--
-- It is often more convenient to view a value of 'Rep'
-- as a constructor and its fields, instead of having to
-- traverse the inner 'NS' structure.

-- |A value @c :: Constr n ks@ specifies a position
--  in a type-level list. It is, in fact, isomorphic to @Fin (length ks)@.
data Constr :: Nat -> [k] -> * where
  CS :: Constr n xs -> Constr (S n) (x : xs)
  CZ ::                Constr Z     (x : xs)

instance (IsNat n) => Show (Constr n xs) where
  show _ = "C" ++ show (getNat (Proxy :: Proxy n))

-- |We can define injections into an n-ary sum from
--  its 'Constr'uctors.
injNS :: Constr n sum -> PoA ki fam (Lkup n sum) -> NS (NP (NA ki fam)) sum
injNS CZ     poa = Here poa
injNS (CS c) poa = There (injNS c poa)

-- |Wrap it in a 'Rep' for convenience.
inj :: Constr n sum -> PoA ki fam (Lkup n sum) -> Rep ki fam sum
inj c = Rep . injNS c

-- |Finally, we can view a sum-of-products as a constructor
--  and a product-of-atoms.
data View :: (kon -> *) -> (Nat -> *) -> [[ Atom kon ]] -> * where
  Tag :: Constr n sum -> PoA ki fam (Lkup n sum) -> View ki fam sum

-- |Unwraps a 'Rep' into a 'View'
sop :: Rep ki fam sum -> View ki fam sum
sop = go . unRep
  where
    go :: NS (NP (NA ki fam)) sum -> View ki fam sum
    go (Here  poa) = Tag CZ poa
    go (There s)   = case go s of
                        Tag c poa -> Tag (CS c) poa

-- * Least Fixpoints
--
-- Finally we tie the recursive knot. Given an interpretation
-- for the constant types, a family of sums-of-products and
-- an index ix into such family, we take the least fixpoint of
-- the representation of the code indexed by ix

-- |Indexed least fixpoints
newtype Fix (ki :: kon -> *) (codes :: [[[ Atom kon ]]]) (n :: Nat)
  = Fix { unFix :: Rep ki (Fix ki codes) (Lkup n codes) }

proxyFixIdx :: Fix ki fam ix -> Proxy ix
proxyFixIdx _ = Proxy

mapMFix :: (Monad m)
        => (forall k . ki k -> m (kj k))
        -> Fix ki fam ix -> m (Fix kj fam ix)
mapMFix fk = (Fix <$>) . hmapMRep fk (mapMFix fk) . unFix

-- |Compare two values of a same fixpoint for equality.
eqFix :: (forall k. ki k -> ki k -> Bool)
      -> Fix ki fam ix -> Fix ki fam ix -> Bool
eqFix p = eqRep p (eqFix p) `on` unFix

-- |Compare two indexes of two fixpoints
heqFixIx :: (IsNat ix , IsNat ix')
         => Fix ki fam ix -> Fix ki fam ix' -> Maybe (ix :~: ix')
heqFixIx fa fb = testEquality (getSNat Proxy) (getSNat Proxy)
