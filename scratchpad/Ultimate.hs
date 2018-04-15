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

data Term (b :: Kind) (rx :: Kind) k where
  Rec   :: Term b rx rx
  Var   :: SNat n -> Term b rx (Lookup_ n b)
  Kon   :: k -> Term b rx k
  (:@:) :: Term b rx (k1 -> k2) -> Term b rx k1 -> Term b rx k2

data Branch (b :: Kind) (rx :: Kind) where
  Exists :: Branch (k -> b) rx -> Branch b rx
  Fields :: [Field b rx]       -> Branch b rx

type DataType rx = [Branch rx rx]

data Field (b :: Kind) (rx :: Kind) where
  Explicit :: Term b rx Type       -> Field b rx
  Implicit :: Term b rx Constraint -> Field b rx

data TyEnv (ks :: [Kind]) where
  TyNil  :: TyEnv '[]
  TyCons :: k -> TyEnv ks -> TyEnv (k ': ks)

data TyEnv_ (ks :: Kind) where
  TyNil_  :: TyEnv_ Type
  TyCons_ :: k -> TyEnv_ ks -> TyEnv_ (k -> ks)

type family Ty (b :: Kind) (rx :: Kind) (t :: Term b rx k)
               (rxty :: rx) (tys :: TyEnv_ b) :: k where
  Ty b rx Rec rxty tys = rxty
  -- and so on and so forth
  Ty (f1 -> fs) rx (Var SZ) rxty (TyCons_ t1 ts) = t1
  Ty (f1 -> f2 -> fs) rx (Var (SS SZ)) rxty (TyCons_ t1 (TyCons_ t2 ts)) = t2
  -- and so on and so forth
  Ty b rx (Kon t)     rxty tys = t
  Ty b rx (t1 :@: t2) rxty tys = (Ty b rx t1 rxty tys) (Ty b rx t2 rxty tys)

data NP (b :: Kind) (rx :: Kind) (fs :: [Field b rx])
        (rxty :: rx) (tys :: TyEnv_ b) where
  NP0 :: NP b rx '[] rxty tys
  NPE :: forall (b :: Kind) (rx :: Kind) (k :: Kind) (tm :: Term b rx Type) rxty tys fs
       . Ty b rx tm rxty tys -> NP b rx fs rxty tys -> NP b rx (Explicit tm ': fs) rxty tys
  NPI :: Ty b rx tm rxty tys => NP b rx fs rxty tys -> NP b rx (Implicit tm ': fs) rxty tys

data NE (b :: Kind) (rx :: Kind) (br :: Branch b rx)
        (rxty :: rx) (tys :: TyEnv_ rx) where
  Es :: forall (b :: Kind) (rx :: Kind) (k :: Kind) (newty :: k)
               (br :: Branch b rx) (rxty :: rx) (tys :: TyEnv_ rx)
      . NE (k -> b) rx br rxty (TyCons_ newty tys) -> NE b rx (Exists br) rxty tys
  Fs :: NP b        rx fs rxty tys -> NE b rx (Fields fs) rxty tys

data NS (rx :: Kind) (dt :: DataType rx)
        (rxty :: rx) (tys :: TyEnv_ rx) where
  H :: NE rx rx c  rxty tys -> NS rx (c ': cs) rxty tys
  T :: NS    rx cs rxty tys -> NS rx (c ': cs) rxty tys

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

class UltimateGeneric (f :: k) where
  type Rep f :: DataType k

  to   :: Proxy f -> Singl k ts -> Apply k f ts -> Fix k (Rep f) ts
  from :: Proxy f -> Singl k ts -> Fix k (Rep f) ts -> Apply k f ts

{-
instance UltimateGeneric [] where
  type Rep [] = '[ Fields '[ ], Fields '[ Explicit (Var SZ), Explicit (Rec :@: (Var SZ)) ] ]

  to _ s@(SCons _ _ SNil) [] = Fix $ H $ Fs $ NP0
  to p s@(SCons _ _ SNil) (x : xs) = Fix $ T $ H $ Fs $ NPE @_ @_ @(Var SZ) x $ NPE (R1 (to p s xs)) $ NP0

  from _ s@(SCons _ _ SNil) (Fix (H (Fs NP0))) = []
  from p s@(SCons _ _ SNil) (Fix (T (H (Fs (NPE x (NPE (R1 xs) NP0)))))) = x : from p s xs

data Eql a b where
  Refl :: Eql a a

instance UltimateGeneric Eql where
  type Rep Eql = '[ Fields '[ Implicit (Kon (~) :@: Var SZ :@: Var (SS SZ)) ] ]

  to   _ s@(SCons _ _ (SCons _ _ SNil)) Refl = Fix $ H $ Fs $ NPI NP0
  from _ s@(SCons _ _ (SCons _ _ SNil)) (Fix (H (Fs (NPI NP0)))) = Refl
-}