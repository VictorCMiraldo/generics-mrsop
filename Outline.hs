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
-- UndecidableInstances needed for Show of Fix
{-# LANGUAGE UndecidableInstances #-}
module Outline where

import Data.Proxy
#define P Proxy :: Proxy
import GHC.TypeLits (TypeError , ErrorMessage(..))

data Nat = S Nat | Z
         deriving (Eq, Show)

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

instance Show (NP p '[]) where
  show NP0 = "END"
instance (Show (p x), Show (NP p xs)) => Show (NP p (x : xs)) where
  showsPrec p (v :* vs)  = showParen (p > 5) $ showsPrec 5 v . showString " :* " . showsPrec 5 vs

instance Eq (NP p '[]) where
  _ == _ = True
instance (Eq (p x), Eq (NP p xs)) => Eq (NP p (x : xs)) where
  (x :* xs) == (y :* ys) = x == y && xs == ys

eqNP :: (forall x. p x -> p x -> Bool)
     -> NP p xs -> NP p xs -> Bool
eqNP _ NP0       NP0       = True
eqNP p (x :* xs) (y :* ys) = p x y && eqNP p xs ys

data NS :: (k -> *) -> [k] -> * where
  There :: NS p xs -> NS p (x : xs)
  Here  :: p x     -> NS p (x : xs)

instance Show (NS p '[]) where
  show _ = error "This code is unreachable"
instance (Show (p x), Show (NS p xs)) => Show (NS p (x : xs)) where
  show (There r) = 'T' : show r
  show (Here  x) = "H (" ++ show x ++ ")"

instance Eq (NS p '[]) where
  _ == _ = error "This code is unreachable"
instance (Eq (p x), Eq (NS p xs)) => Eq (NS p (x : xs)) where
  There x == There y = x == y
  Here  x == Here  y = x == y
  _       == _       = False

eqNS :: (forall x. p x -> p x -> Bool)
     -> NS p xs -> NS p xs -> Bool
eqNS p (There u) (There v) = eqNS p u v
eqNS p (Here  u) (Here  v) = p u v
eqNS _ _         _         = False

data NA  :: (kon -> *) -> (Nat -> *) -> Atom kon -> * where
  NA_I :: fam k -> NA ki fam (I k) 
  NA_K :: ki  k -> NA ki fam (K k)

-- https://stackoverflow.com/questions/9082642/implementing-the-show-class
instance (Show (fam k)) => Show (NA ki fam (I k)) where
  showsPrec p (NA_I v) = showParen (p > 10) $ showString "I-" . showsPrec 11 v
instance (Show (ki  k)) => Show (NA ki fam (K k)) where
  showsPrec p (NA_K v) = showParen (p > 10) $ showString "K " . showsPrec 11 v

instance Eq (fam k) => Eq (NA ki fam (I k)) where
  NA_I x == NA_I y = x == y
instance Eq (ki  k) => Eq (NA ki fam (K k)) where
  NA_K x == NA_K y = x == y

eqNA :: (forall k.  ki  k  -> ki  k  -> Bool)
     -> (forall ix. fam ix -> fam ix -> Bool)
     -> NA ki fam l -> NA ki fam l -> Bool
eqNA kp _  (NA_K u) (NA_K v) = kp u v
eqNA _  fp (NA_I u) (NA_I v) = fp u v

type Rep (ki :: kon -> *) (fam :: Nat -> *) = NS (Poa ki fam)
type Poa (ki :: kon -> *) (fam :: Nat -> *) = NP (NA  ki fam)

type f :-> g = forall n . f n -> g n

hmapNA :: f :-> g -> NA ki f a -> NA ki g a
hmapNA nat (NA_I f) = NA_I (nat f)
hmapNA nat (NA_K i) = NA_K i

hmapNP :: f :-> g -> NP f ks -> NP g ks
hmapNP f NP0       = NP0
hmapNP f (k :* ks) = f k :* hmapNP f ks

hmapNS :: f :-> g -> NS f ks -> NS g ks
hmapNS f (Here p) = Here (f p)
hmapNS f (There p) = There (hmapNS f p)

hmapRep :: f :-> g -> Rep ki f c -> Rep ki g c
hmapRep f = hmapNS (hmapNP (hmapNA f))

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
--Tag :: (c : Constr sum) -> Poa fam (TypeOf c) -> View fam sum
  Tag :: Constr n sum -> Poa ki fam (Lkup n sum) -> View ki fam sum

sop :: Rep ki fam sum -> View ki fam sum
sop (Here  poa) = Tag CZ poa
sop (There s)   = case sop s of
                    Tag c poa -> Tag (CS c) poa

-- * Recursive Knot

type family Lkup (n :: Nat) (ks :: [k]) :: k where
  Lkup Z     (k : ks) = k
  Lkup (S n) (k : ks) = Lkup n ks
  Lkup _     '[]      = TypeError (Text "Lkup index too big")

newtype Fix (ki :: kon -> *) (fam :: Family(kon)) (n :: Nat)
  = Fix { unFix :: Rep ki (Fix ki fam) (Lkup n fam) }

instance Show (Rep ki (Fix ki fam) (Lkup n fam)) => Show (Fix ki fam n) where
  show (Fix x) = show x

deriving instance Eq (Rep ki (Fix ki fam) (Lkup n fam)) => Eq (Fix ki fam n)

eqFix :: (forall k. ki k -> ki k -> Bool)
      -> Fix ki fam ix -> Fix ki fam ix -> Bool
eqFix p (Fix u) (Fix v) = eqNS (eqNP (eqNA p (eqFix p))) u v

-- * Cannonical Example

data R a = a :>: [R a] deriving Show

value1, value2 :: R Int
value1 = 1 :>: [2 :>: [], 3 :>: []]
value2 = 1 :>: [2 :>: []]

type List = '[ '[] , '[I (S Z) , I Z] ]
type RT   = '[ '[K KInt , I Z] ]

data Kon = KInt | KFloat
         deriving (Eq, Show)

data Singl (kon :: Kon) where
  SInt   :: Int   -> Singl KInt
  SFloat :: Float -> Singl KFloat

deriving instance Show (Singl k)
deriving instance Eq   (Singl k)

eqSingl :: Singl k -> Singl k -> Bool
eqSingl = (==)

type Rose = '[List , RT]


nil :: Fix Singl Rose Z
nil = Fix (Here NP0)

cons :: Fix Singl Rose (S Z) -> Fix Singl Rose Z -> Fix Singl Rose Z
cons x xs = Fix (There $ Here (NA_I x :* NA_I xs :* NP0))

fork :: Int -> Fix Singl Rose Z -> Fix Singl Rose (S Z)
fork x xs = Fix (Here (NA_K (SInt x) :* NA_I xs :* NP0))

-- * Metadata a la generics-sop

type ModuleName = String
type DatatypeName = String
type ConstructorName = String
type FieldName = String

data DatatypeInfo :: [[Atom kon]] -> * where
  ADT :: ModuleName -> DatatypeName -> NP ConstructorInfo c
      -> DatatypeInfo c
  New :: ModuleName -> DatatypeName -> ConstructorInfo '[ c ]
      -> DatatypeInfo '[ '[ c ]]

data ConstructorInfo :: [Atom kon] -> * where
  Constructor :: ConstructorName -> ConstructorInfo xs
  Infix       :: ConstructorName -> ConstructorInfo '[ x , y ]
  Record      :: ConstructorName -> NP FieldInfo xs -> ConstructorInfo xs

data FieldInfo :: Atom kon -> * where
  FieldInfo :: FieldName -> FieldInfo k
