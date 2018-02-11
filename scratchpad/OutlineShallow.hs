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
module OutlineShallow where

import Data.Proxy
#define P Proxy :: Proxy
import GHC.TypeLits (TypeError , ErrorMessage(..))
import GHC.Exts (Constraint)

import Data.Function (on)

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

-- |Singleton Term-level natural
data SNat :: Nat -> * where
  SZ ::           SNat Z
  SS :: SNat n -> SNat (S n)



-- |Type-level list lookup
type family Lkup (n :: Nat) (ks :: [k]) :: k where
  Lkup Z     (k : ks) = k
  Lkup (S n) (k : ks) = Lkup n ks
  Lkup _     '[]      = TypeError (Text "Lkup index too big")

-- |Also list lookup, but for kind * only.
data El :: Nat -> [*] -> * where
  EZ :: x       -> El Z     (x ': xs) 
  ES :: El n xs -> El (S n) (x ': xs) 

class IsElem (tys :: [*]) (ix :: Nat)  where
  projEl :: El ix tys   -> Lkup ix tys 
  injEl  :: Lkup ix tys -> El ix tys 
instance IsElem (ty : tys) Z where
  projEl (EZ x) = x
  injEl x       = EZ x
instance (IsElem tys n) => (IsElem (tw : tys) (S n)) where
  projEl (ES x) = projEl x
  injEl x       = ES (injEl x)
-- instance (TypeError (Text "Empty list has no elements")) => IsElem '[] n


-- * Codes

data Atom kon
  = K kon
  | I Nat
  deriving (Eq, Show)

-- can't use type synonyms as they are
-- not promoted to kinds with -XDataKinds yet.
-- https://ghc.haskell.org/trac/ghc/wiki/GhcKinds#Kindsynonymsfromtypesynonympromotion
#define Prod(kon)   [Atom kon]
#define Sum(kon)    [Prod(kon)]
#define Family(kon) [Sum(kon)]

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

data NA  :: (kon -> *) -> [*] -> Atom kon -> * where
  NA_I :: (IsNat k) => El k fam -> NA ki fam (I k) 
  NA_K :: ki  k    -> NA ki fam (K k)

eqNA :: (forall k.  ki  k  -> ki  k  -> Bool)
     -> (forall ix. El ix fam -> El ix fam -> Bool)
     -> NA ki fam l -> NA ki fam l -> Bool
eqNA kp _  (NA_K u) (NA_K v) = kp u v
eqNA _  fp (NA_I u) (NA_I v) = fp u v

type Rep (ki :: kon -> *) (fam :: [*]) = NS (Poa ki fam)
type Poa (ki :: kon -> *) (fam :: [*]) = NP (NA  ki fam)

type f :-> g = forall n . f n -> g n


hmapNA :: (forall ix . IsNat ix => El ix f -> El ix g)
       -> NA ki f a -> NA ki g a
hmapNA nat (NA_I f) = NA_I (nat f)
hmapNA nat (NA_K i) = NA_K i

hmapNP :: f :-> g -> NP f ks -> NP g ks
hmapNP f NP0       = NP0
hmapNP f (k :* ks) = f k :* hmapNP f ks

hmapNS :: f :-> g -> NS f ks -> NS g ks
hmapNS f (Here p) = Here (f p)
hmapNS f (There p) = There (hmapNS f p)

hmapRep :: (forall ix . IsNat ix => El ix f -> El ix g) -> Rep ki f c -> Rep ki g c
hmapRep f = hmapNS (hmapNP (hmapNA f))

class Family ki (fam :: [*]) where
  type family Codes fam :: [[[Atom kon]]]

  from :: (IsNat ix) => El ix fam -> Rep ki fam (Lkup ix (Codes fam))

  to'  :: SNat ix -> Rep ki fam (Lkup ix (Codes fam)) -> El ix fam

  to   :: (IsNat ix) => Rep ki fam (Lkup ix (Codes fam)) -> El ix fam
  to = to' (getSNat (Proxy :: Proxy ix))

from' :: forall fam ix ki . (Family ki fam , IsNat ix)
      => El ix fam -> Rep ki fam (Lkup ix (Codes fam))
from' = from

-- We can define our version of compos.
compos :: forall fam ix ki . (Family ki fam, IsNat ix)
       => Proxy ki
       -> (forall ix . (IsNat ix) => El ix fam -> El ix fam)
       -> El ix fam -> El ix fam
compos pki f = to . hmapRep f . from' @fam @ix @ki

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

instance Family Singl FamRose where
  type Codes FamRose = CodesRose
  
  from (ES (EZ (a :>: as))) = Here (NA_K (SInt a) :* NA_I (EZ as) :* NP0)
  from (ES (EZ (Leaf a)))   = There (Here (NA_K (SInt a) :* NP0))
  from (EZ [])              = Here NP0
  from (EZ (x:xs))          = There (Here (NA_I (ES (EZ x)) :* NA_I (EZ xs) :* NP0))
  
  to' SZ (Here NP0)
    = EZ []
  to' SZ (There (Here (NA_I (ES (EZ x)) :* NA_I (EZ xs) :* NP0)))
    = EZ (x : xs)
  to' (SS SZ) (Here (NA_K (SInt a) :* NA_I (EZ as) :* NP0))
    = ES (EZ (a :>: as))
  to' (SS SZ) (There (Here (NA_K (SInt a) :* NP0)))
    = ES (EZ (Leaf a))


-- * SOP functionality

-- Constr n l === Fin (length l)
--
data Constr :: Nat -> [k] -> * where
  CS :: Constr n xs -> Constr (S n) (x : xs)
  CZ ::                Constr Z     (x : xs)

deriving instance Show (Constr n xs)

inj :: Constr n sum -> Poa ki fam (Lkup n sum) -> Rep ki fam sum
inj CZ     poa = Here poa
inj (CS c) poa = There (inj c poa)

data View :: (kon -> *) -> [*] -> Sum(kon) -> * where
  Tag :: Constr n sum -> Poa ki fam (Lkup n sum) -> View ki fam sum

sop :: Rep ki fam sum -> View ki fam sum
sop (Here  poa) = Tag CZ poa
sop (There s)   = case sop s of
                    Tag c poa -> Tag (CS c) poa

-- * Equality changes significantly!

type family All (f :: k -> Constraint) (tys :: [k]) :: Constraint where
  All f '[]       = ()
  All f (x ': xs) = (f x , All f xs)

eqRep :: (All Eq fam)
      => (forall k . ki k -> ki k -> Bool)
      -> Rep ki fam c -> Rep ki fam c -> Bool
eqRep kp t u = eqNS (eqNP (eqNA kp go)) t u
  where
    go :: (All Eq fam) => El xi fam -> El xi fam -> Bool
    go (EZ x) (EZ y) = x == y
    go (ES t) (ES u) = go t u

instance Eq (R Int) where
  x == y = eqRep eqSingl (from' @FamRose (ES (EZ x))) (from (ES (EZ y)))

test :: Bool
test = value1 == value1
    && value2 /= value1

-- Compos works

normalize :: R Int -> R Int
normalize = projEl . go . (ES . EZ) 
  where
    go :: (IsNat ix) => El ix FamRose -> El ix FamRose
    go (ES (EZ (Leaf a))) = (ES (EZ (a :>: [])))
    go x                  = compos (Proxy :: Proxy Singl) go x
  
