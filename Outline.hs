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

data NS :: (k -> *) -> [k] -> * where
  There :: NS p xs -> NS p (x : xs)
  Here  :: p x     -> NS p (x : xs)

instance Show (NS p '[]) where
  show _ = error "This code is unreachable"
instance (Show (p x), Show (NS p xs)) => Show (NS p (x : xs)) where
  show (There r) = 'T' : show r
  show (Here  x) = "H (" ++ show x ++ ")"

data NA  :: (kon -> *) -> (Nat -> *) -> Atom kon -> * where
  NA_I :: fam k -> NA ki fam (I k) 
  NA_K :: ki  k -> NA ki fam (K k)

-- https://stackoverflow.com/questions/9082642/implementing-the-show-class
instance (Show (fam k)) => Show (NA ki fam (I k)) where
  showsPrec p (NA_I v) = showParen (p > 10) $ showString "I-" . showsPrec 11 v
instance (Show (ki  k)) => Show (NA ki fam (K k)) where
  showsPrec p (NA_K v) = showParen (p > 10) $ showString "K " . showsPrec 11 v

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

-- * Cannonical Example

data R a = a :>: [R a] deriving Show

value :: R Int
value = 1 :>: [2 :>: [], 3 :>: []]

type List = '[ '[] , '[I (S Z) , I Z] ]
type RT   = '[ '[K KInt , I Z] ]

data Kon = KInt
         deriving (Eq, Show)

data Singl (kon :: Kon) where
  SInt :: Int -> Singl KInt 

type Rose = '[List , RT]


nil :: Fix Singl Rose Z
nil = Fix (Here NP0)

cons :: Fix Singl Rose (S Z) -> Fix Singl Rose Z -> Fix Singl Rose Z
cons x xs = Fix (There $ Here (NA_I x :* NA_I xs :* NP0))

fork :: Int -> Fix Singl Rose Z -> Fix Singl Rose (S Z)
fork x xs = Fix (Here (NA_K (SInt x) :* NA_I xs :* NP0))