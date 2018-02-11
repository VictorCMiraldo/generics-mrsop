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
data El :: [*] -> Nat -> * where
  EZ :: x       -> El (x ': xs) Z 
  ES :: El xs n -> El (x ': xs) (S n)

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
#define Phiily(kon) [Sum(kon)]

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

hmapRep :: (forall ix . IsNat ix => f ix -> g ix) -> Rep ki f c -> Rep ki g c
hmapRep f = Rep . hmapNS (hmapNP (hmapNA f)) . unRep

class Family (ki :: kon -> *) (fam :: [*]) where
  type family Codes fam :: [[[Atom kon]]]

  ffrom :: (IsNat ix) => El fam ix -> Rep ki (El fam) (Lkup ix (Codes fam))
  fto   :: (IsNat ix) => Rep ki (El fam) (Lkup ix (Codes fam)) -> El fam ix
  fto   = fto' (getSNat (Proxy :: Proxy ix))

  fto'  :: SNat ix -> Rep ki (El fam) (Lkup ix (Codes fam)) -> El fam ix

ffrom' :: forall ki fam ix . (Family ki fam , IsNat ix)
      => El fam ix -> Rep ki (El fam) (Lkup ix (Codes fam))
ffrom' = ffrom

-- We can define our version of compos.
fcompos :: forall ki fam ix . (Family ki fam , IsNat ix)
        => Proxy ki
        -> (forall iy . (IsNat iy) => El fam iy -> El fam iy)
        -> El fam ix -> El fam ix
fcompos pki f = fto . hmapRep f . ffrom' @ki @fam

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
  
  ffrom (ES (EZ (a :>: as))) = Rep $ Here (NA_K (SInt a) :* NA_I (EZ as) :* NP0)
  ffrom (ES (EZ (Leaf a)))   = Rep $ There (Here (NA_K (SInt a) :* NP0))
  ffrom (EZ [])              = Rep $ Here NP0
  ffrom (EZ (x:xs))          = Rep $ There (Here (NA_I (ES (EZ x)) :* NA_I (EZ xs) :* NP0))
  
  fto' SZ (Rep (Here NP0))
    = EZ []
  fto' SZ (Rep (There (Here (NA_I (ES (EZ x)) :* NA_I (EZ xs) :* NP0))))
    = EZ (x : xs)
  fto' (SS SZ) (Rep (Here (NA_K (SInt a) :* NA_I (EZ as) :* NP0)))
    = ES (EZ (a :>: as))
  fto' (SS SZ) (Rep (There (Here (NA_K (SInt a) :* NP0))))
    = ES (EZ (Leaf a))

-- * SOP functionality
{-
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
-}
-- * Equality changes significantly!

type family All (f :: k -> Constraint) (tys :: [k]) :: Constraint where
  All f '[]       = ()
  All f (x ': xs) = (f x , All f xs)
{-
eqRep ::(Family ki fam)
      => (forall k . ki k -> ki k -> Bool)
      -> Rep ki (El fam) c -> Rep ki (El fam) c -> Bool
eqRep kp t u = eqNS (eqNP (eqNA kp (go (Proxy :: Proxy ki)))) t u
  where
    go :: (Family ki fam) => Proxy ki -> El fam xi -> El fam xi -> Bool
    go p (EZ x) (EZ y) = eqRep kp (from x) (from y)
    go p (ES t) (ES u) = go p t u

instance Eq (R Int) where
  x == y = eqRep eqSingl (from' @FamRose (ES (EZ x))) (from (ES (EZ y)))

test :: Bool
test = value1 == value1
    && value2 /= value1
-}
-- Compos works
class IsElem (tys :: [*]) (ix :: Nat) where
  projEl :: El tys ix   -> Lkup ix tys 
  injEl  :: Lkup ix tys -> El tys ix 
instance IsElem (ty : tys) Z where
  projEl (EZ x) = x
  injEl x       = EZ x
instance (IsElem tys n) => (IsElem (tw : tys) (S n)) where
  projEl (ES x) = projEl x
  injEl x       = ES (injEl x)
-- instance (TypeError (Text "Empty list has no elements")) => IsElem '[] n

onEl :: (IsElem tys ix) => SNat ix -> (El tys ix -> El tys ix) -> Lkup ix tys -> Lkup ix tys
onEl _ f = projEl . f . injEl

normalize :: R Int -> R Int
normalize = onEl (SS SZ) go
  where
    go :: (IsNat ix) => El FamRose ix -> El FamRose ix
    go (ES (EZ (Leaf a))) = injEl (a :>: [])
    go x                  = fcompos (Proxy :: Proxy Singl) go x

