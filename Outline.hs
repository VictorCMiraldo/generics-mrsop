{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS_GHC -cpp #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs     #-}
module Outline where

import Data.Proxy
#define P Proxy :: Proxy
import GHC.TypeLits (TypeError , ErrorMessage(..))

data Nat = S Nat | Z

-- * Codes

data Atom
  = K Kon
  | I Nat

-- can't use type synonyms as they are
-- not promoted to kinds with -XDataKinds yet.
-- https://ghc.haskell.org/trac/ghc/wiki/GhcKinds#Kindsynonymsfromtypesynonympromotion
#define Prod    [Atom]
#define Sum     [Prod]
#define Family  [Sum]

-- * Opaque Types

data Kon = KInt
type family Konst (k :: Kon) :: * where
  Konst KInt = Int

-- * Interpretation of Codes

infixr 5 :*
data NP :: (k -> *) -> [k] -> * where
  NP0  :: NP p '[]
  (:*) :: p x -> NP p xs -> NP p (x : xs)

data NS :: (k -> *) -> [k] -> * where
  There :: NS p xs -> NS p (x : xs)
  Here  :: p x     -> NS p (x : xs)

data NA  :: (Nat -> *) -> Atom -> * where
  NA_I :: fam k   -> NA fam (I k) 
  NA_K :: Konst k -> NA fam (K k)

type Rep (fam :: Nat -> *) = NS (Poa fam)
type Poa (fam :: Nat -> *) = NP (NA fam)

type f :-> g = forall n . f n -> g n

hmapNA :: f :-> g -> NA f a -> NA g a
hmapNA nat (NA_I f) = NA_I (nat f)
hmapNA nat (NA_K i) = NA_K i

hmapNP :: f :-> g -> NP f ks -> NP g ks
hmapNP f NP0       = NP0
hmapNP f (k :* ks) = f k :* hmapNP f ks

hmapNS :: f :-> g -> NS f ks -> NS g ks
hmapNS f (Here p) = Here (f p)
hmapNS f (There p) = There (hmapNS f p)

hmapRep :: f :-> g -> Rep f c -> Rep g c
hmapRep f = hmapNS (hmapNP (hmapNA f))

-- * SOP functionality

-- Constr n l === Fin (length l)
--
data Constr :: Nat -> [k] -> * where
  CS :: Constr n xs -> Constr (S n) (x : xs)
  CZ ::                Constr Z     (x : xs)

inj :: Constr n sum -> Poa fam (Lkup n sum) -> Rep fam sum
inj CZ     poa = Here poa
inj (CS c) poa = There (inj c poa)

data View :: (Nat -> *) -> Sum -> * where
--Tag :: (c : Constr sum) -> Poa fam (TypeOf c) -> View fam sum
  Tag :: Constr n sum -> Poa fam (Lkup n sum) -> View fam sum
{-
deriving instance Show (NA n s)
deriving instance Show (Poa n s)
deriving instance Show (Constr n s)
deriving instance Show (View n s)
-}

sop :: Rep fam sum -> View fam sum
sop (Here  poa) = Tag CZ poa
sop (There s)   = case sop s of
                    Tag c poa -> Tag (CS c) poa

-- * Recursive Knot

type family Lkup (n :: Nat) (ks :: [k]) :: k where
  Lkup Z     (k : ks) = k
  Lkup (S n) (k : ks) = Lkup n ks
  Lkup _     '[]      = TypeError (Text "Lkup index too big")

newtype Fix (fam :: Family) (n :: Nat)
  = Fix { unFix :: Rep (Fix fam) (Lkup n fam) }

-- * Cannonical Example

type List = '[ '[] , '[I (S Z) , I Z] ]
type RT   = '[ '[K KInt , I Z] ]

type Rose = '[List , RT]

nil :: Fix Rose Z
nil = Fix (Here NP0)

cons :: Fix Rose (S Z) -> Fix Rose Z -> Fix Rose Z
cons x xs = Fix (There $ Here (NA_I x :* NA_I xs :* NP0))

fork :: Int -> Fix Rose Z -> Fix Rose (S Z)
fork x xs = Fix (Here (NA_K x :* NA_I xs :* NP0))

-- * Multirec

class Element ty (fam :: Family) where
  type Idx ty fam :: Nat

  from :: ty -> Fix fam (Idx ty fam)
  to   :: Fix fam (Idx ty fam) -> ty

-- * Usage

data R a = a :>: [R a] deriving Show

instance Element [R Int] Rose where
  type Idx [R Int] Rose = Z
  
  from []     = nil 
  from (x:xs) = cons (from x) (from xs)

  to (Fix x) = case sop x of
                    Tag CZ p -> []
                    Tag (CS CZ) (NA_I vx :* NA_I vxs :* NP0)
                       -> (to vx : to vxs)

instance Element (R Int) Rose where
  type Idx (R Int) Rose = (S Z)

  from (i :>: is) = fork i (from is)
  to (Fix (Here (NA_K i :* NA_I xs :* NP0))) = i :>: to xs


