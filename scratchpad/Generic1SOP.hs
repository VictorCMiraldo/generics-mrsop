{-# language DataKinds #-}
{-# language ConstraintKinds #-}
{-# language ExplicitNamespaces #-}
{-# language TypeOperators #-}
{-# language GADTs #-}
{-# language TypeFamilies #-}
{-# language PolyKinds #-}
{-# language ExistentialQuantification #-}
{-# language InstanceSigs #-}
{-# language TypeApplications #-}
{-# language FlexibleInstances #-}
{-# language MultiParamTypeClasses #-}
{-# language FunctionalDependencies #-}
{-# language PatternSynonyms #-}
{-# language TypeInType #-}
{-# language ScopedTypeVariables #-}
{-# language FlexibleContexts #-}
{-# language FlexibleInstances #-}
{-# language UndecidableInstances #-}
module Generic1SOP where

import Data.Kind (type (*), type Type, Constraint)

data Atom = Var | Rec (* -> *) | Kon (*)

data NS :: (k -> *) -> [k] -> * where
  Here   :: f k      -> NS f (k ': ks)
  There  :: NS f ks  -> NS f (k ': ks)

infixr 5 :*
data NP :: (k -> *) -> [k] -> * where
  Nil  ::                    NP f '[]
  (:*) :: f x -> NP f xs ->  NP f (x ': xs)

data NA :: * -> Atom -> * where
  V :: a   -> NA a Var
  R :: f a -> NA a (Rec f)
  K :: k   -> NA a (Kon k)

type SOP1 c a = NS (NP (NA a)) c

class Generic1SOP (f :: * -> *) where
  type Code1 f :: [[Atom]]
  from :: f a -> SOP1 (Code1 f) a
  to   :: SOP1 (Code1 f) a -> f a

data Tree a = Leaf | Node (Tree a) a (Tree a)

instance Generic1SOP Tree where
  type Code1 Tree = '[ '[], '[ Rec Tree, Var, Rec Tree ] ]

  from Leaf         = Here Nil
  from (Node l x r) = There $ Here $ R l :* V x :* R r :* Nil

  to (Here Nil) = Leaf
  to (There (Here (R l :* V x :* R r :* Nil))) = Node l x r

type family AllRec2 c xs :: Constraint where
  AllRec2 c '[]       = ()
  AllRec2 c (x ': xs) = (AllRec c x, AllRec2 c xs)

type family AllRec c xs :: Constraint where
  AllRec c '[]       = ()
  AllRec c (Rec x ': xs) = (c x, AllRec c xs)
  AllRec c (x ': xs) = AllRec c xs

type family All2 c xs :: Constraint where
  All2 c '[]       = ()
  All2 c (x ': xs) = (All c x, All2 c xs)

type family All c xs :: Constraint where
  All c '[]       = ()
  All c (x ': xs) = (c x, All c xs)

class OnRec (c :: (* -> *) -> Constraint) (a :: Atom)
instance c f => OnRec c (Rec f)
instance OnRec c Var
instance OnRec c (Kon k)

class FunctorRec (a :: Atom)
instance Functor f => FunctorRec (Rec f)
instance FunctorRec Var
instance FunctorRec (Kon k)

gfmap :: forall f a b
       . (Generic1SOP f, AllRec2 Functor (Code1 f))
      => (a -> b) -> f a -> f b
gfmap f = to . goS . from
  where
    goS :: AllRec2 Functor xs
        => NS (NP (NA a)) xs -> NS (NP (NA b)) xs
    goS (Here  x) = Here  (goP x)
    goS (There x) = There (goS x)
        
    goP :: AllRec Functor xs
        => NP (NA a) xs -> NP (NA b) xs
    goP Nil         = Nil
    goP (R x :* xs) = (R $ fmap f x) :* goP xs
    goP (V x :* xs) = V (f x) :* goP xs
    goP (K x :* xs) = K x     :* goP xs
