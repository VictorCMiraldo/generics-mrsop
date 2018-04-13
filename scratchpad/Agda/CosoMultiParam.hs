{-# language DataKinds #-}
{-# language TypeInType #-}
{-# language ConstraintKinds #-}
{-# language ExplicitNamespaces #-}
{-# language TypeOperators #-}
{-# language GADTs #-}
{-# language TypeFamilies #-}
{-# language PolyKinds #-}
{-# language InstanceSigs #-}
{-# language ScopedTypeVariables #-}
{-# language TypeApplications #-}
{-# language MultiParamTypeClasses #-}
{-# language FlexibleInstances #-}
{-# language FunctionalDependencies #-}
module CosoMultiParam where

import Data.Kind (type (*), type Type)
import GHC.Exts (Constraint)

type Kind = (*)

type DT  ps = [Con ps]
type Con (ps :: [Kind]) = ( [ps :->: Constraint]
                          , [Field Type (ps :->: Type) (Type -> Type)] )
data Field k v post
           = Kon k
           | Var v
           | Rec post
           
type family (xs :: [Kind]) :->: (r :: Kind) :: Kind where
  '[]       :->: r = r
  (x ': xs) :->: r = x -> (xs :->: r)

data NS (f :: a -> k -> *) (xs :: [a]) (ps :: k) where
  Here  :: f x ps     -> NS f (x ': xs) ps
  There :: NS f xa ps -> NS f (x ': xs) ps

data HList xs where
  HNil  :: HList '[]
  HCons :: x -> HList xs -> HList (x ': xs)

type family ApplyList ks (ts :: HList ks) (f :: ks :->: r) :: r where
  ApplyList '[]       HNil           f = f
  ApplyList (x ': xs) (HCons tx txs) f = ApplyList xs txs (f tx)

{-
type family ApplyConstraints ks (ts :: HList ks) (f :: [ks :->: Constraint]) :: Constraint where
  ApplyConstraints ks ts '[] = ()
  ApplyConstraints ks ts (c ': cs) = (ApplyList ks ts c, ApplyConstraints ks ts cs)
-}

{-
data NC (f :: a -> (ks :->: Type)) (con :: ([ks :->: Constraint], [a])) (ps :: HList ks) where
  B :: ApplyConstraints ks ps cs => NP f xs ps -> NC f '(cs, xs) ps

type family All cs x :: Constraint where
  All '[]       x = ()
  All (c ': cs) x = (c x, All cs x)
-}

infixr 5 :*:
data NP f xs (ps :: HList ks) where
  NP0   ::                         NP f '[] ps
  (:*:) :: f x ps -> NP f xs ps -> NP f (x ': xs) ps

data NF r field (ps :: HList ks) where
  K  :: t                        -> NF r (Kon t) ps
  V  :: ApplyList ks ps g        -> NF r (Var g) ps
  R  :: post (ApplyList ks ps r) -> NF r (Rec post) ps

type N r dt ps = NS (NP (NF r)) dt ps

newtype Fix dt ps = Fix { unFix :: N (Fix dt) dt ps }

{-
newtype Id a = Id { getId :: a }
type List = '[ '( '[], '[] )
             , '( '[], '[Var Id, Rec Id] ) ]

-- CANNOT RETURN A POLYMORPHIC TYPE FROM FAMILY!
-- THUS, WE CANNOT HAVE SOMETHING WHICH TAKES THE
-- LIST OF KINDS AND TURNS IT INTO A POLY THING

{-
class UltimateGeneric ks (f :: ks :->: *) where
  type Rep f :: DT ks
  to   :: forall (ts :: HList ks). ApplyList ks ts f -> Fix (Rep f) ts
  from :: forall (ts :: HList ks). Fix (Rep f) ts -> ApplyList ks ts f
-}
-}