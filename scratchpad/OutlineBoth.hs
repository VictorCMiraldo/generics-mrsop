{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS_GHC -cpp #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs     #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}
module OutlineBoth where

import GHC.TypeLits (TypeError , ErrorMessage(..))
import GHC.Exts (Constraint)

import Data.Function (on)

data Proxy (a :: k) = Proxy

data Nat = S Nat | Z
         deriving (Eq, Show)

proxyUnsuc :: Proxy (S n) -> Proxy n
proxyUnsuc _ = Proxy

-- |And their conversion to term-level integers.
class IsNat (n :: Nat) where
  getSNat :: Proxy n -> SNat n
instance IsNat Z where
  getSNat p = SZ
instance IsNat n => IsNat (S n) where
  getSNat p = SS (getSNat $ proxyUnsuc p)

getSNat' :: forall (n :: Nat). IsNat n => SNat n
getSNat' = getSNat (Proxy :: Proxy n)

-- |Singleton Term-level natural
data SNat :: Nat -> * where
  SZ ::           SNat Z
  SS :: SNat n -> SNat (S n)

-- |Type-level list lookup
type family Lkup (n :: Nat) (ks :: [k]) :: k where
  Lkup Z     (k : ks) = k
  Lkup (S n) (k : ks) = Lkup n ks
  Lkup _     '[]      = TypeError (Text "Lkup index too big")

-- |Type-level list search
type family Ix (x :: k) (xs :: [k]) :: Nat where
  Ix x (x ': xs) = Z
  Ix y (x ': xs) = S (Ix y xs)
  Ix y '[]       = TypeError (Text "Element not in the list")

data Proof (c :: Constraint) where
  Proof :: c => Proof c

-- |Also list lookup, but for kind * only.
data El :: [*] -> Nat -> * where
  El :: IsNat ix => Lkup ix fam -> El fam ix

-- * Codes

data Atom kon
  = K kon
  | I Nat
  deriving (Eq, Show)

-- * Interpretation of Codes

infixr 5 :*
data NP :: (k -> *) -> [k] -> * where
  NP0  :: NP p '[]
  (:*) :: p x -> NP p xs -> NP p (x : xs)

eqNP :: (forall x. p x -> p x -> Bool)
     -> NP p xs -> NP p xs -> Bool
eqNP _ NP0       NP0       = True
eqNP p (x :* xs) (y :* ys) = p x y && eqNP p xs ys

data NS :: (k -> *) -> [k] -> * where
  There :: NS p xs -> NS p (x : xs)
  Here  :: p x     -> NS p (x : xs)

eqNS :: (forall x. p x -> p x -> Bool)
     -> NS p xs -> NS p xs -> Bool
eqNS p (There u) (There v) = eqNS p u v
eqNS p (Here  u) (Here  v) = p u v
eqNS _ _         _         = False

data NA  :: (kon -> *) -> (Nat -> *) -> Atom kon -> * where
  NA_I :: (IsNat k) => phi k -> NA ki phi (I k) 
  NA_K ::              ki  k -> NA ki phi (K k)

eqNA :: (forall k.  ki  k  -> ki  k  -> Bool)
     -> (forall ix. phi ix -> phi ix -> Bool)
     -> NA ki phi l -> NA ki phi l -> Bool
eqNA kp _  (NA_K u) (NA_K v) = kp u v
eqNA _  fp (NA_I u) (NA_I v) = fp u v

-- TODO: Make rep into a newtype; this should resolve the problem
--       when unifying ki's
type Poa (ki :: kon -> *) (phi :: Nat -> *) = NP (NA  ki phi)

type f :-> g = forall n . f n -> g n

hmapNA :: (forall ix . IsNat ix => f ix -> g ix) -> NA ki f a -> NA ki g a
hmapNA nat (NA_I f) = NA_I (nat f)
hmapNA nat (NA_K i) = NA_K i

hmapNP :: f :-> g -> NP f ks -> NP g ks
hmapNP f NP0       = NP0
hmapNP f (k :* ks) = f k :* hmapNP f ks

hmapNS :: f :-> g -> NS f ks -> NS g ks
hmapNS f (Here p) = Here (f p)
hmapNS f (There p) = There (hmapNS f p)

newtype Rep (ki :: kon -> *) (phi :: Nat -> *) (c :: [[Atom kon]])
  = Rep { unRep :: NS (Poa ki phi) c }

newtype Fix (ki :: kon -> *) (codes :: [[[Atom kon]]]) (n :: Nat)
  = Fix { unFix :: Rep ki (Fix ki codes) (Lkup n codes) }

hmapRep :: (forall ix . IsNat ix => f ix -> g ix) -> Rep ki f c -> Rep ki g c
hmapRep f = Rep . hmapNS (hmapNP (hmapNA f)) . unRep

class Family (ki :: kon -> *) (fam :: [*]) (codes :: [[[Atom kon]]])
  | fam -> ki codes, ki codes -> fam where
  
  stoIx   :: SNat ix -> Lkup ix fam -> Rep ki (El fam) (Lkup ix codes)
  sfromIx :: SNat ix -> Rep ki (El fam) (Lkup ix codes) -> Lkup ix fam

  dtoIx   :: SNat ix -> Lkup ix fam -> Rep ki (Fix ki codes) (Lkup ix codes)

proof :: Proxy fam -> Proxy ty -> Proof (Lkup (Ix ty fam) fam ~ ty)
proof _ = undefined

sto :: forall fam ty ki codes. (Family ki fam codes, IsNat (Ix ty fam))
    => ty -> Rep ki (El fam) (Lkup (Ix ty fam) codes)
sto = case proof (Proxy :: Proxy fam) (Proxy :: Proxy ty) of
        Proof -> stoIx (getSNat' @(Ix ty fam))

stoIx' :: forall fam ty ki codes ix. (Family ki fam codes)
     => SNat ix -> Lkup ix fam -> Rep ki (El fam) (Lkup ix codes)
stoIx' = stoIx

sfromIx' :: forall fam ty ki codes ix. (Family ki fam codes)
         => SNat ix -> Rep ki (El fam) (Lkup ix codes) -> Lkup ix fam
sfromIx' = sfromIx

liftEl :: forall fam ki codes. (Family ki fam codes)
       => (forall iy. SNat iy -> Lkup iy fam -> Lkup iy fam)
       -> (forall iy. IsNat iy => El fam iy -> El fam iy)
liftEl f = p
  where p :: forall iy. IsNat iy => El fam iy -> El fam iy
        p (El x) = El (f (getSNat' @iy) x) 

composIx :: forall ki fam codes ix.
            (Family ki fam codes)
         => Proxy fam
         -> (forall iy. SNat iy -> Lkup iy fam -> Lkup iy fam)
         -> SNat ix -> Lkup ix fam -> Lkup ix fam
composIx _ g ix = sfromIx' @fam ix
                . hmapRep (liftEl g)
                . stoIx' @fam ix

compos :: forall fam ki codes ty.
          (Family ki fam codes, IsNat (Ix ty fam))
       => Proxy fam
       -> (forall iy. SNat iy -> Lkup iy fam -> Lkup iy fam)
       -> ty -> ty
compos p g = case proof (Proxy :: Proxy fam) (Proxy :: Proxy ty) of
               Proof -> composIx p g (getSNat' @(Ix ty fam))

-- * Cannonical Example

data R a = a :>: [R a]
         | Leaf a
         deriving Show

value1, value2 :: R Int
value1 = 1 :>: [2 :>: [], 3 :>: []]
value2 = 1 :>: [2 :>: [] , Leaf 12]
value3 = 3 :>: [Leaf 23 , value1 , value2]

type List = '[ '[] , '[I (S Z) , I Z] ]
type RT   = '[ '[K KInt , I Z] , '[K KInt] ]

data Kon = KInt | KFloat
         deriving (Eq, Show)

data Singl (kon :: Kon) where
  SInt   :: Int   -> Singl KInt
  SFloat :: Float -> Singl KFloat

deriving instance Show (Singl k)
deriving instance Eq   (Singl k)

eqSingl :: Singl k -> Singl k -> Bool
eqSingl = (==)

type CodesRose = '[List , RT]

type FamRose = '[ [R Int] , R Int] 

instance Family Singl FamRose CodesRose where

  stoIx (SS SZ) (a :>: as) = Rep $ Here (NA_K (SInt a) :* NA_I (El as) :* NP0)
  stoIx (SS SZ) (Leaf a)   = Rep $ There (Here (NA_K (SInt a) :* NP0))
  stoIx SZ []              = Rep $ Here NP0
  stoIx SZ (x:xs)          = Rep $ There (Here (NA_I (El x) :* NA_I (El xs) :* NP0))

  sfromIx SZ (Rep (Here NP0))
    = []
  sfromIx SZ (Rep (There (Here (NA_I (El x) :* NA_I (El xs) :* NP0))))
    = (x : xs)
  sfromIx (SS SZ) (Rep (Here (NA_K (SInt a) :* NA_I (El as) :* NP0)))
    = (a :>: as)
  sfromIx (SS SZ) (Rep (There (Here (NA_K (SInt a) :* NP0))))
    = (Leaf a)

normalize :: R Int -> R Int
normalize = go (SS SZ)
  where
    go :: forall iy. SNat iy -> Lkup iy FamRose -> Lkup iy FamRose
    go (SS SZ) (Leaf a) = (a :>: [])
    go iy      x        = composIx (Proxy :: Proxy FamRose) go iy x