{-# LANGUAGE UndecidableInstances #-}
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

import Generics.MRSOP.Base.Internal.NS
import Generics.MRSOP.Base.Internal.NP
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
  NA_I :: phi k -> NA ki phi (I k) 
  NA_K :: ki  k -> NA ki phi (K k)

-- https://stackoverflow.com/questions/9082642/implementing-the-show-class
instance (Show (fam k)) => Show (NA ki fam (I k)) where
  showsPrec p (NA_I v) = showParen (p > 10) $ showString "I-" . showsPrec 11 v
instance (Show (ki  k)) => Show (NA ki fam (K k)) where
  showsPrec p (NA_K v) = showParen (p > 10) $ showString "K " . showsPrec 11 v

-- ** Equality and Map

eqNA :: (forall k  . ki  k  -> ki  k  -> Bool)
     -> (forall ix . fam ix -> fam ix -> Bool)
     -> NA ki fam l -> NA ki fam l -> Bool
eqNA kp _  (NA_K u) (NA_K v) = kp u v
eqNA _  fp (NA_I u) (NA_I v) = fp u v

mapNA :: f :-> g -> NA ki f a -> NA ki g a
mapNA nat (NA_I f) = NA_I (nat f)
mapNA nat (NA_K i) = NA_K i

-- * Representation of Codes
--
-- Codes are represented using the 'Rep' newtype,
-- which wraps an n-ary sum of n-ary products. 

-- |Representation of codes.
newtype Rep (ki :: kon -> *) (phi :: Nat -> *) (code :: [[Atom kon]])
  = Rep { unRep :: NS (PoA ki phi) code }

instance Show (NS (PoA ki phi) code) => Show (Rep ki phi code) where
  show (Rep x) = show x

-- |Product of Atoms is a handy synonym to have.
type PoA (ki :: kon -> *) (phi :: Nat -> *) = NP (NA ki phi)

-- ** Equality and Map

-- |We can map over representations
hmapRep :: f :-> g -> Rep ki f c -> Rep ki g c
hmapRep f = Rep . mapNS (mapNP (mapNA f)) . unRep

-- |And compare them for equality
eqRep :: (forall k  . ki  k  -> ki  k  -> Bool)
      -> (forall ix . fam ix -> fam ix -> Bool)
      -> Rep ki fam c -> Rep ki fam c -> Bool
eqRep kp fp = eqNS (eqNP $ eqNA kp fp) `on` unRep

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
newtype Fix (ki :: kon -> *) (fam :: [[[ Atom kon ]]]) (n :: Nat)
  = Fix { unFix :: Rep ki (Fix ki fam) (Lkup n fam) }

instance Show (Rep ki (Fix ki fam) (Lkup n fam)) => Show (Fix ki fam n) where
  show (Fix x) = show x

-- |Compare two values of a same fixpoint for equality.
eqFix :: (forall k. ki k -> ki k -> Bool)
      -> Fix ki fam ix -> Fix ki fam ix -> Bool
eqFix p = eqRep p (eqFix p) `on` unFix

-- |Compare two indexes of two fixpoints
heqFixIx :: (IsNat ix , IsNat ix')
         => Fix ki fam ix -> Fix ki fam ix' -> Maybe (ix :~: ix')
heqFixIx fa fb = testEquality getSNat getSNat
