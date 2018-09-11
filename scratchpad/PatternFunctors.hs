{-# language PolyKinds, DataKinds, KindSignatures, TypeInType #-}
{-# language GADTs, TypeOperators, TypeFamilies, ConstraintKinds #-}
{-# language ExistentialQuantification #-}
{-# language MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
module PatternFunctors where

import Data.Kind

data U x         = U
data (f :+: g) x = InL (f x) | InR (g x)
data (f :*: g) x = f x :*: g x

data TyVar (d :: *) k where
  VZ :: TyVar (x -> xs) x
  VS :: TyVar xs k -> TyVar (x -> xs) k

data Atom (d :: *) k where
  Var   :: TyVar d k -> Atom d k
  Kon   :: k         -> Atom d k
  (:@:) :: Atom d (k1 -> k2) -> Atom d k1 -> Atom d k2

type f :$: x = Kon f :@: x
type a :~: b = Kon (~) :@: a :@: b

type V0  = Var VZ
type V1  = Var (VS VZ)
type V2  = Var (VS (VS VZ))

infixr 5 :&&:
data LoT (d :: *) where
  LoT0    ::                LoT (*)
  (:&&:)  :: k -> LoT ks -> LoT (k -> ks)

type family Ty (d :: *) (tys :: LoT d) (t :: Atom d k) :: k where
  Ty (k -> ks) (t :&&: ts) (Var VZ)     = t
  Ty (k -> ks) (t :&&: ts) (Var (VS v)) = Ty ks ts (Var v)
  Ty d tys (Kon t)   = t
  Ty d tys (f :@: x) = (Ty d tys f) (Ty d tys x)

newtype F (t :: Atom d (*)) (x :: LoT d) = F { unF :: Ty d x t }
data C (t :: Atom d Constraint) (x :: LoT d) where
  C :: Ty d x t => C t x

data E (k :: *) (f :: LoT (k -> d) -> *) (x :: LoT d) where
  E :: forall (k :: *) (t :: k) (d :: *) (f :: LoT (k -> d) -> *) (x :: LoT d)
     . f (t :&&: x) -> E k f x

data ApplyT k (f :: k) (tys :: LoT k) :: * where
  A0  :: { unA0  :: f } -> ApplyT (*) f  LoT0
  Arg :: { unArg :: ApplyT ks (f t) ts } -> ApplyT (k -> ks) f (t :&&: ts)

data SLoT dtk (tys :: LoT dtk) where
  SLoT0  ::               SLoT (*)       LoT0
  SLoTA  :: SLoT ks ts -> SLoT (k -> ks) (t :&&: ts)

class SSLoT k (tys :: LoT k) where
  sslot :: SLoT k tys
instance SSLoT (*) LoT0 where
  sslot = SLoT0
instance SSLoT ks ts => SSLoT (k -> ks) (t :&&: ts) where
  sslot = SLoTA sslot

class Generic (f :: k) where
  type Rep f :: LoT k -> *
  from :: ApplyT k f x -> Rep f x
  to :: SLoT k x -> Rep f x -> ApplyT k f x

instance Generic [] where
  type Rep [] = U :+: (F V0 :*: F (Kon [] :@: V0))

  from (Arg (A0 []))     = InL U
  from (Arg (A0 (x:xs))) = InR (F x :*: F xs)

  to (SLoTA SLoT0) (InL U) = Arg $ A0 $ []
  to (SLoTA SLoT0) (InR (F x :*: F xs)) = Arg $ A0 $ x : xs

data Equals a b where
  Refl :: Equals a a

instance Generic Equals where
  type Rep Equals = C (V0 :~: V1)

  from (Arg (Arg (A0 Refl))) = C
  to (SLoTA (SLoTA SLoT0)) C = Arg $ Arg $ A0 $ Refl

data X where
  X :: a -> X

instance Generic X where
  type Rep X = E (*) (F V0)

  from (A0 (X x)) = E (F x)
  to SLoT0 (E (F x)) = A0 $ X x