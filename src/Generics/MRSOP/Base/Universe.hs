{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE PatternSynonyms      #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
-- |Wraps the definitions of 'NP' and 'NS'
--  into Representations ('Rep'), essentially providing
--  the universe view over sums-of-products.
module Generics.MRSOP.Base.Universe where

import Data.Function (on)
import Data.Type.Equality
import Data.Proxy

import Data.Functor.Const
import Control.Monad

import Generics.MRSOP.Base.NS
import Generics.MRSOP.Base.NP
import Generics.MRSOP.Util

-- * Universe of Codes
--
-- $universeOfCodes
--
-- We will use nested lists to represent the Sums-of-Products
-- structure. The atoms, however, will be parametrized by a kind
-- used to index what are the types that are opaque to the library.
--

-- |Atoms can be either opaque types, @kon@, or
--  type variables, @Nat@.
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

instance (EqHO phi, EqHO ki) => EqHO (NA ki phi) where
  eqHO = eqNA eqHO eqHO

instance (EqHO phi, EqHO ki) => Eq (NA ki phi at) where
  (==) = eqHO

instance (ShowHO phi, ShowHO ki) => ShowHO (NA ki phi) where
  showHO (NA_I i) = "(NA_I " ++ showHO i ++ ")"
  showHO (NA_K k) = "(NA_K " ++ showHO k ++ ")"

instance (ShowHO phi, ShowHO ki) => Show (NA ki phi at) where
  show = showHO

instance (TestEquality ki) => TestEquality (NA ki phi) where
  testEquality (NA_I i) (NA_K k) = Nothing
  testEquality (NA_K i) (NA_I k) = Nothing
  testEquality (NA_I i) (NA_I i') =
    case testEquality (sNatFixIdx i) (sNatFixIdx i') of
      Just Refl -> Just Refl
      Nothing -> Nothing
  testEquality (NA_K k) (NA_K k') =
    -- we learn that
    -- a ~ (K k1)
    -- b ~ (K k2)
    case testEquality k k' of
      -- we learn that  k1 ~ k2
      Just Refl ->
        -- thus we learn that a ~ b. Q.e.d
        Just Refl
      Nothing -> Nothing


-- ** Map, Elim and Zip

-- |Maps a natural transformation over an atom interpretation
mapNA :: (forall k  .             ki k  -> kj k)
      -> (forall ix . IsNat ix => f  ix -> g  ix)
      -> NA ki f a -> NA kj g a
mapNA fk fi (NA_I f) = NA_I (fi f)
mapNA fk fi (NA_K k) = NA_K (fk k)

-- |Maps a monadic natural transformation over an atom interpretation
mapNAM :: (Monad m)
       => (forall k  .             ki k  -> m (kj k))
       -> (forall ix . IsNat ix => f  ix -> m (g  ix))
       -> NA ki f a -> m (NA kj g a)
mapNAM fk fi (NA_K k) = NA_K <$> fk k
mapNAM fk fi (NA_I f) = NA_I <$> fi f

-- |Eliminates an atom interpretation
elimNA :: (forall k .            ki  k -> b)
       -> (forall k . IsNat k => phi k -> b)
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
-- $representationOfCodes
--
-- Codes are represented using the 'Rep' newtype,
-- which wraps an n-ary sum of n-ary products. Note it receives two
-- functors: @ki@ and @phi@, to interpret opaque types and type variables
-- respectively.

-- |Representation of codes.
newtype Rep (ki :: kon -> *) (phi :: Nat -> *) (code :: [[Atom kon]])
  = Rep { unRep :: NS (PoA ki phi) code }

instance (EqHO phi, EqHO ki) => EqHO (Rep ki phi) where
  eqHO = eqRep eqHO eqHO

instance (EqHO phi, EqHO ki) => Eq (Rep ki phi at) where
  (==) = eqHO
  
-- |Product of Atoms is a handy synonym to have.
type PoA (ki :: kon -> *) (phi :: Nat -> *) = NP (NA ki phi)

-- ** Map, Elim and Zip
--
-- $mapElimAndZip
--
-- Just like for 'NS', 'NP' and 'NA', we provide
-- a couple convenient functions working over
-- a 'Rep'. These are just the cannonical combination
-- of their homonym versions in 'NS', 'NP' or 'NA'.

-- |Maps over a representation.
mapRep :: (forall ix . IsNat ix => f  ix -> g ix)
       -> Rep ki f c -> Rep ki g c
mapRep = bimapRep id

-- |Maps a monadic function over a representation.
mapRepM :: (Monad m)
        => (forall ix . IsNat ix => f  ix -> m (g  ix))
        -> Rep ki f c -> m (Rep ki g c)
mapRepM = bimapRepM return

-- |Maps over both indexes of a representation.
bimapRep :: (forall k  .             ki k  -> kj k)
         -> (forall ix . IsNat ix => f  ix -> g ix)
         -> Rep ki f c -> Rep kj g c
bimapRep fk fi = Rep . mapNS (mapNP (mapNA fk fi)) . unRep

-- |Monadic version of 'bimapRep'
bimapRepM :: (Monad m)
          => (forall k  .             ki k  -> m (kj k))
          -> (forall ix . IsNat ix => f  ix -> m (g  ix))
          -> Rep ki f c -> m (Rep kj g c)
bimapRepM fk fi = (Rep <$>) . mapNSM (mapNPM (mapNAM fk fi)) . unRep

-- |Zip two representations together, in case they are made with the same
--  constructor.
--
--  > zipRep (Here (NA_I x :* NP0)) (Here (NA_I y :* NP0))
--  >   = return $ Here (NA_I (x :*: y) :* NP0)
--
--  > zipRep (Here (NA_I x :* NP0)) (There (Here ...))
--  >   = mzero
--
zipRep :: (MonadPlus m)
       => Rep ki f c -> Rep kj g c
       -> m (Rep (ki :*: kj) (f :*: g) c)
zipRep (Rep t) (Rep u)
  = Rep . mapNS (mapNP (uncurry' zipNA) . uncurry' zipNP) <$> zipNS t u

-- |Monadic eliminator; This is just the cannonical combination of
--  'elimNS', 'elimNPM' and 'elimNA'.
elimRepM :: (Monad m)
         => (forall k . ki k -> m a)
         -> (forall k . IsNat k => f  k -> m a)
         -> ([a] -> m b)
         -> Rep ki f c -> m b
elimRepM fk fi cat
  = cat <.> elimNS (elimNPM (elimNA fk fi)) . unRep

-- |Pure eliminator.
elimRep :: (forall k .            ki k -> a)
        -> (forall k . IsNat k => f  k -> a)
        -> ([a] -> b)
        -> Rep ki f c -> b
elimRep kp fp cat
  = elimNS (cat . elimNP (elimNA kp fp)) . unRep

-- |Compares two 'Rep' for equality; again, cannonical combination
--  of 'eqNS', 'eqNP' and 'eqNA'
eqRep :: (forall k  . ki  k  -> ki  k  -> Bool)
      -> (forall ix . fam ix -> fam ix -> Bool)
      -> Rep ki fam c -> Rep ki fam c -> Bool
eqRep kp fp t = maybe False (elimRep (uncurry' kp) (uncurry' fp) and)
              . zipRep t 

-- * SOP functionality
--
-- $sopFunctionality
--
-- It is often more convenient to view a value of 'Rep'
-- as a constructor and its fields, instead of having to
-- traverse the inner 'NS' structure.

-- |A value @c :: Constr ks n@ specifies a position
--  in a type-level list. It is, in fact, isomorphic to @Fin (length ks)@.
data Constr :: [k] -> Nat -> * where
  CS :: Constr xs n -> Constr (x : xs) (S n)
  CZ ::                Constr (x : xs) Z

instance TestEquality (Constr codes) where
  testEquality CZ     CZ     = Just Refl
  testEquality (CS x) (CS y) = apply (Refl :: S :~: S) <$> testEquality x y
  testEquality _      _      = Nothing

instance (IsNat n) => Show (Constr xs n) where
  show _ = "C" ++ show (getNat (Proxy :: Proxy n))

-- |We can define injections into an n-ary sum from
--  its 'Constr'uctors
injNS :: Constr sum n -> PoA ki fam (Lkup n sum) -> NS (NP (NA ki fam)) sum
injNS CZ     poa = Here poa
injNS (CS c) poa = There (injNS c poa)

-- |Wrap it in a 'Rep' for convenience.
inj :: Constr sum n -> PoA ki fam (Lkup n sum) -> Rep ki fam sum
inj c = Rep . injNS c

-- | Inverse of 'injNS'.  Given some Constructor, see if Rep is of this constructor
matchNS :: Constr sum c -> NS (NP (NA ki fam)) sum -> Maybe (PoA ki fam (Lkup c sum))
matchNS CZ (Here ps) = Just ps
matchNS (CS c) (There x) = matchNS c x
matchNS _ _ = Nothing

-- | Inverse of 'inj'. Given some Constructor, see if Rep is of this constructor
match :: Constr sum c -> Rep ki fam sum -> Maybe (PoA ki fam (Lkup c sum))
match c (Rep x) = matchNS c x

-- |Finally, we can view a sum-of-products as a constructor
--  and a product-of-atoms.
data View :: (kon -> *) -> (Nat -> *) -> [[ Atom kon ]] -> * where
  Tag :: IsNat n => Constr sum n -> PoA ki fam (Lkup n sum) -> View ki fam sum

-- |Unwraps a 'Rep' into a 'View'
sop :: Rep ki fam sum -> View ki fam sum
sop = go . unRep
  where
    go :: NS (NP (NA ki fam)) sum -> View ki fam sum
    go (Here  poa) = Tag CZ poa
    go (There s)   = case go s of
                        Tag c poa -> Tag (CS c) poa

-- |Wraps a 'View' into a 'Rep'
fromView :: View ki fam sum -> Rep ki fam sum
fromView (Tag c x) = inj c x

-- * Least Fixpoints
--
-- $leastFixpoints
--
-- Finally we tie the recursive knot. Given an interpretation
-- for the constant types, a family of sums-of-products and
-- an index ix into such family, we take the least fixpoint of
-- the representation of the code indexed by ix

-- |Indexed least fixpoints
{-newtype Fix (ki :: kon -> *) (codes :: [[[ Atom kon ]]]) (n :: Nat)
  = Fix { unFix :: Rep ki (Fix ki codes) (Lkup n codes) }
-}


-- | Annotated version of Fix.   This is basically the 'Cofree' datatype,
-- but for n-ary functors
data AnnFix (ki :: kon -> *) (codes :: [[[Atom kon]]]) (phi :: Nat -> *) (n :: Nat) =
  AnnFix (phi n)
         (Rep ki (AnnFix ki codes phi) (Lkup n codes))

type Fix ki codes = AnnFix ki codes (Const ())

pattern Fix x = AnnFix (Const ()) x

unFix :: Fix ki codes ix -> Rep ki (Fix ki codes) (Lkup ix codes)
unFix (Fix x) = x

-- | Catamorphism over fixpoints
cata :: (IsNat ix)
  => (forall iy. IsNat iy => Rep ki phi (Lkup iy codes) -> phi iy)
  -> Fix ki codes ix
  -> phi ix
cata f (Fix x) = f (mapRep (cata f) x)


getAnn :: AnnFix ki codes ann ix -> ann ix
getAnn (AnnFix a x) = a

annCata :: IsNat ix
        => (forall iy. IsNat iy => chi iy -> Rep ki phi (Lkup iy codes) -> phi iy)
        -> AnnFix ki codes chi ix
        -> phi ix
annCata f (AnnFix a x) = f a (mapRep (annCata f) x)

-- | Forget the annotations
forgetAnn :: AnnFix ki codes a ix -> Fix ki codes ix
forgetAnn (AnnFix _ rep) = Fix (mapRep forgetAnn rep)

instance EqHO ki => EqHO (Fix ki codes) where
  eqHO = eqFix eqHO

-- |Retrieves the index of a 'Fix'
proxyFixIdx :: phi ix -> Proxy ix
proxyFixIdx _ = Proxy

sNatFixIdx :: IsNat ix => phi ix -> SNat ix
sNatFixIdx x = getSNat (proxyFixIdx x)

-- |Maps over the values of opaque types within the
--  fixpoint.
mapFixM :: (Monad m)
        => (forall k . ki k -> m (kj k))
        -> Fix ki fam ix -> m (Fix kj fam ix)
mapFixM fk = (Fix <$>) . bimapRepM fk (mapFixM fk) . unFix

-- |Compare two values of a same fixpoint for equality.
eqFix :: (forall k. ki k -> ki k -> Bool)
      -> Fix ki fam ix -> Fix ki fam ix -> Bool
eqFix p = eqRep p (eqFix p) `on` unFix

instance EqHO ki => Eq (Fix ki codes ix) where
  (==) = eqFix eqHO

-- |Compare two indexes of two fixpoints
--  Note we can't use a 'testEquality' instance because
--  of the 'IsNat' constraint.
heqFixIx :: (IsNat ix , IsNat ix')
         => Fix ki fam ix -> Fix ki fam ix' -> Maybe (ix :~: ix')
heqFixIx fa fb = testEquality (getSNat Proxy) (getSNat Proxy)

