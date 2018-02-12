{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances #-}
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

-- |Type-level list index
type family Idx (ty :: k) (xs :: [k]) :: Nat where
  Idx x (x ': ys) = Z
  Idx x (y ': ys) = S (Idx x ys)
  Idx x '[]       = TypeError (Text "Element not found")

-- |Also list lookup, but for kind * only.
data El :: [*] -> Nat -> * where
  El :: IsNat ix => {unEl :: Lkup ix fam} -> El fam ix


getElSNat :: forall ix ls. El ls ix -> SNat ix
getElSNat (El _) = getSNat' @ix

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

crushNP :: forall r p xs. 
           (forall x. p x -> r)
        -> ([r] -> r)
        -> NP p xs -> r
crushNP step combine = combine . listify
  where listify :: forall ys. NP p ys -> [r]
        listify NP0 = []
        listify (x :* xs) = step x : listify xs

data NS :: (k -> *) -> [k] -> * where
  There :: NS p xs -> NS p (x : xs)
  Here  :: p x     -> NS p (x : xs)

eqNS :: (forall x. p x -> p x -> Bool)
     -> NS p xs -> NS p xs -> Bool
eqNS p (There u) (There v) = eqNS p u v
eqNS p (Here  u) (Here  v) = p u v
eqNS _ _         _         = False

crushNS :: (forall x. p x -> r)
        -> NS p xs -> r
crushNS step (There u) = crushNS step u
crushNS step (Here  u) = step u

data NA  :: (kon -> *) -> (Nat -> *) -> Atom kon -> * where
  NA_I :: (IsNat k) => phi k -> NA ki phi (I k) 
  NA_K ::              ki  k -> NA ki phi (K k)

eqNA :: (forall k.  ki  k  -> ki  k  -> Bool)
     -> (forall ix. phi ix -> phi ix -> Bool)
     -> NA ki phi l -> NA ki phi l -> Bool
eqNA kp _  (NA_K u) (NA_K v) = kp u v
eqNA _  fp (NA_I u) (NA_I v) = fp u v

crushNA :: (forall k. ki k -> r)
        -> (forall x. p  x -> r)
        -> NA ki p l -> r
crushNA kstep _ (NA_K v) = kstep v
crushNA _ pstep (NA_I v) = pstep v

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

crushRep :: (forall k. ki k -> r)
         -> (forall x. f  x -> r)
         -> ([r] -> r) -> Rep ki f c -> r
crushRep kstep fstep combine = crushNS (crushNP (crushNA kstep fstep) combine) . unRep

newtype Fix (ki :: kon -> *) (codes :: [[[Atom kon]]]) (n :: Nat)
  = Fix { unFix :: Rep ki (Fix ki codes) (Lkup n codes) }

crushFix :: forall ki codes ix r. (forall k. ki k -> r) -> ([r] -> r)
         -> Fix ki codes ix -> r
crushFix kstep combine = crushRep kstep (crushFix kstep combine) combine . unFix

class Family (ki :: kon -> *) (fam :: [*]) (codes :: [[[Atom kon]]])
  | fam -> ki codes, ki codes -> fam where
  
  sto'   :: SNat ix -> El fam ix -> Rep ki (El fam) (Lkup ix codes)
  sfrom' :: SNat ix -> Rep ki (El fam) (Lkup ix codes) -> El fam ix

sto :: forall fam ki codes ix
     . (Family ki fam codes)
    => El fam ix -> Rep ki (El fam) (Lkup ix codes)
sto el = sto' (getElSNat el) el

sfrom :: forall fam ki codes ix
       . (Family ki fam codes , IsNat ix)
      => Rep ki (El fam) (Lkup ix codes) -> El fam ix  
sfrom el = sfrom' (getSNat' @ix) el


-- Finally, a deep embedding comming for "free" 
dto :: forall ix ki fam codes
     . (Family ki fam codes)
    => El fam ix
    -> Rep ki (Fix ki codes) (Lkup ix codes)
dto = hmapRep (Fix . dto) . sto @fam

compos :: forall ki fam codes ix
        . (Family ki fam codes, IsNat ix)
       => (forall iy . IsNat iy => SNat iy -> El fam iy -> El fam iy)
       -> El fam ix -> El fam ix
compos f = sfrom @fam
         . hmapRep (\x -> f (getElSNat x) x)
         . sto @fam

-- |Smart injectors

into :: forall fam ty ki codes ix
      . (Family ki fam codes,
         ix ~ Idx ty fam, Lkup ix fam ~ ty, IsNat ix)
     => ty -> El fam ix
into = El

shallow :: forall fam ty ki codes ix
         . (Family ki fam codes,
           ix ~ Idx ty fam, Lkup ix fam ~ ty, IsNat ix)
        => ty -> Rep ki (El fam) (Lkup ix codes)
shallow = sto . into

deep :: forall fam ty ki codes ix
      . (Family ki fam codes,
         ix ~ Idx ty fam, Lkup ix fam ~ ty, IsNat ix)
     => ty -> Rep ki (Fix ki codes) (Lkup ix codes)
deep = dto . into

crush :: forall fam ty ki codes ix r
      . (Family ki fam codes,
         ix ~ Idx ty fam, Lkup ix fam ~ ty, IsNat ix)
     => Proxy fam
     -> (forall k. ki k -> r) -> ([r] -> r)
     -> ty -> r
crush _ kstep combine = crushFix @ki @codes @ix kstep combine . Fix . deep @fam

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
  sto' (SS SZ) (El (a :>: as)) = Rep $ Here (NA_K (SInt a) :* NA_I (El as) :* NP0)
  sto' (SS SZ) (El (Leaf a))   = Rep $ There (Here (NA_K (SInt a) :* NP0))
  sto' SZ (El [])              = Rep $ Here NP0
  sto' SZ (El (x:xs))          = Rep $ There (Here (NA_I (El x) :* NA_I (El xs) :* NP0))

  sfrom' SZ (Rep (Here NP0))
    = El []
  sfrom' SZ (Rep (There (Here (NA_I (El x) :* NA_I (El xs) :* NP0))))
    = El (x : xs)
  sfrom' (SS SZ) (Rep (Here (NA_K (SInt a) :* NA_I (El as) :* NP0)))
    = El (a :>: as)
  sfrom' (SS SZ) (Rep (There (Here (NA_K (SInt a) :* NP0))))
    = El (Leaf a)

normalize :: R Int -> R Int
normalize = unEl . go (SS SZ) . into
  where
    go :: forall iy. (IsNat iy) => SNat iy -> El FamRose iy -> El FamRose iy
    go (SS SZ) (El (Leaf a)) = El (a :>: [])
    go _       x             = compos go x

eqRep :: forall ki fam codes c . (Family ki fam codes)
      => (forall k . ki k -> ki k -> Bool)
      -> Rep ki (Fix ki codes) c -> Rep ki (Fix ki codes) c -> Bool
eqRep kp (Rep t) (Rep u) = eqNS (eqNP (eqNA kp go)) t u
  where
    go :: forall ix . Fix ki codes ix -> Fix ki codes ix -> Bool
    go (Fix u) (Fix v) = eqRep kp u v

instance Eq (R Int) where
  x == y = eqRep eqSingl (deep @FamRose x) (deep @FamRose y)

test :: Bool
test = value1 == value1
    && value2 /= value1

sumTree :: R Int -> Int
sumTree = crush (Proxy :: Proxy FamRose) k sum
  where k :: Singl x -> Int
        k (SInt n) = n

{-
{-
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

data View :: (kon -> *) -> (Nat -> *) -> Sum(kon) -> * where
  Tag :: Constr n sum -> Poa ki fam (Lkup n sum) -> View ki fam sum

sop :: Rep ki fam sum -> View ki fam sum
sop (Here  poa) = Tag CZ poa
sop (There s)   = case sop s of
                    Tag c poa -> Tag (CS c) poa
-}

-- * Equality changes significantly!
{-


elLift2a :: (Family ki fam)
         => (forall ix . IsNat ix => SNat ix -> Lkup ix fam -> Lkup ix fam -> a)
         -> (forall ix . IsNat ix => El fam ix -> El fam ix -> a)
elLift2a f x y = let iy = elNat x
              in f iy (projEl iy x) (projEl iy y)
-}

eqRep :: forall ki fam codes c . (Family ki fam codes)
      => (forall k . ki k -> ki k -> Bool)
      -> Rep ki (Fix ki codes) c -> Rep ki (Fix ki codes) c -> Bool
eqRep kp (Rep t) (Rep u) = eqNS (eqNP (eqNA kp go)) t u
  where
    go :: forall ix . Fix ki codes ix -> Fix ki codes ix -> Bool
    go (Fix u) (Fix v) = eqRep kp u v

instance Eq (R Int) where
  x == y = eqRep eqSingl (dfrom (SS SZ) x) (dfrom (SS SZ) y)

test :: Bool
test = value1 == value1
    && value2 /= value1
-}
-- Compos works
{-
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
-}
