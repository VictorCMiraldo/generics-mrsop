{-# language DataKinds #-}
{-# language TypeInType #-}
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
module CosoMultiParam where

import Data.Kind (type (*), type Type)
import GHC.Exts (Constraint)
import GHC.TypeLits (TypeError, ErrorMessage(..))

type Kind = (*)

data Nat = Z | S Nat

data SNat (n :: Nat) where
  SZ :: SNat Z
  SS :: SNat n -> SNat (S n)

type family Lookup (ix :: Nat) (lst :: [k]) :: k where
  Lookup n     '[]       = TypeError (Text "Index not found")
  Lookup Z     (x ': xs) = x
  Lookup (S n) (x ': xs) = Lookup n xs

type family Lookup_ (ix :: Nat) (lst :: Kind) :: Kind where
  -- Lookup_ n     Type       = TypeError (Text "Index not found")
  Lookup_ Z     (x -> xs) = x
  Lookup_ (S n) (x -> xs) = Lookup_ n xs

data Term (rx :: Kind) k where
  Rec   :: Term rx rx
  Var   :: SNat n -> Term rx (Lookup_ n rx)
  Kon   :: k -> Term rx k
  (:@:) :: Term rx (k1 -> k2) -> Term rx k1 -> Term rx k2

type Branch   rx = [Field rx]
type DataType rx = [Branch rx]

data Field (rx :: Kind) where
  Explicit :: Term rx Type       -> Field rx
  Implicit :: Term rx Constraint -> Field rx

data TyEnv (ks :: [Kind]) where
  TyNil  :: TyEnv '[]
  TyCons :: k -> TyEnv ks -> TyEnv (k ': ks)

data TyEnv_ (ks :: Kind) where
  TyNil_  :: TyEnv_ Type
  TyCons_ :: k -> TyEnv_ ks -> TyEnv_ (k -> ks)

type family Ty (rx :: Kind) (t :: Term rx k)
               (rxty :: rx) (tys :: TyEnv_ rx) :: k where
  Ty rx Rec rxty tys = rxty
  -- and so on and so forth
  Ty (f1 -> fs) (Var SZ) rxty (TyCons_ t1 ts) = t1
  Ty (f1 -> f2 -> fs) (Var (SS SZ)) rxty (TyCons_ t1 (TyCons_ t2 ts)) = t2
  -- and so on and so forth
  Ty rx (Kon t)     rxty tys = t
  Ty rx (t1 :@: t2) rxty tys = (Ty rx t1 rxty tys) (Ty rx t2 rxty tys)

data NP (rx :: Kind) (fs :: [Field rx])
        (rxty :: rx) (tys :: TyEnv_ rx) where
  NP0 :: NP rx '[] rxty tys
  NPE :: forall (rx :: Kind) (k :: Kind) (tm :: Term rx Type) rxty tys fs
       . Ty rx tm rxty tys -> NP rx fs rxty tys -> NP rx (Explicit tm ': fs) rxty tys
  NPI :: Ty rx tm rxty tys => NP rx fs rxty tys -> NP rx (Implicit tm ': fs) rxty tys

data NS (rx :: Kind) (dt :: DataType rx)
        (rxty :: rx) (tys :: TyEnv_ rx) where
  H :: NP rx c  rxty tys -> NS rx (c ': cs) rxty tys
  T :: NS rx cs rxty tys -> NS rx (c ': cs) rxty tys

data family Fix' (rx :: Kind) (dt :: DataType rx) :: rx
data instance Fix' Type dt
  = R0 (Fix Type dt TyNil_)
data instance Fix' (k1 -> Type) dt a
  = R1 (Fix (k1 -> Type) dt (TyCons_ a TyNil_))
data instance Fix' (k1 -> k2 -> Type) dt a b
  = R2 (Fix (k1 -> k2 -> Type) dt (TyCons_ a (TyCons_ b TyNil_)))

newtype Fix rx (dt :: DataType rx) (tys :: TyEnv_ rx)
  = Fix (NS rx dt (Fix' rx dt) tys)

type family Apply k (f :: k) (tys :: TyEnv_ k) :: Type where
  Apply Type      f TyNil_ = f
  Apply (k -> ks) f (TyCons_ t ts) = Apply ks (f t) ts

data Proxy (a :: k) = Proxy

data Singl k (ts :: TyEnv_ k) where
  SNil  :: Singl Type TyNil_
  SCons :: Proxy k -> Proxy a -> Singl ks as -> Singl (k -> ks) (TyCons_ a as)

class UltimateGeneric k (f :: k) | f -> k where
  type Rep f :: DataType k

  to   :: Proxy f -> Singl k ts -> Apply k f ts -> Fix k (Rep f) ts
  from :: Proxy f -> Singl k ts -> Fix k (Rep f) ts -> Apply k f ts

instance UltimateGeneric (* -> *) [] where
  type Rep [] = '[ '[ ], '[ Explicit (Var SZ), Explicit (Rec :@: (Var SZ)) ] ]

  to _ s@(SCons _ _ SNil) [] = Fix $ H $ NP0
  to p s@(SCons _ _ SNil) (x : xs) = Fix $ T $ H $ NPE @_ @_ @(Var SZ) x $ NPE (R1 (to p s xs)) $ NP0

  from _ s@(SCons _ _ SNil) (Fix (H NP0)) = []
  from p s@(SCons _ _ SNil) (Fix (T (H (NPE x (NPE (R1 xs) NP0))))) = x : from p s xs

data Eql a b where
  Refl :: Eql a a

instance UltimateGeneric (k -> k -> *) Eql where
  type Rep Eql = '[ '[ Implicit (Kon (~) :@: Var SZ :@: Var (SS SZ)) ] ]

  to   _ s@(SCons _ _ (SCons _ _ SNil)) Refl = Fix $ H $ NPI NP0
  from _ s@(SCons _ _ (SCons _ _ SNil)) (Fix (H (NPI NP0))) = Refl

show :: UltimateGeneric (*) x => x -> String
show = undefined