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
{-# language PatternSynonyms #-}
module CosoMultiParam where

import Data.Kind (type (*), type Type)
import GHC.Exts (Constraint)
import GHC.TypeLits (TypeError, ErrorMessage(..))

type Kind = (*)

data Nat = Z | S Nat

data SNat (n :: Nat) where
  SZ :: SNat Z
  SS :: SNat n -> SNat (S n)

-- SYNTAX
-- ======

  -- dtk = data type kind
  -- fix = type of the fixpoint operator

type family Pos (ix :: Nat) (dtk :: Kind) :: Kind where
  -- Pos n     Type       = TypeError (Text "Index not found")
  Pos Z     (x -> xs) = x
  Pos (S n) (x -> xs) = Pos n xs

data Term (dtk :: Kind) k where
  Var   :: SNat n -> Term dtk (Pos n dtk)
  Rec   :: Term dtk dtk
  Kon   :: k -> Term dtk k
  (:@:) :: Term dtk (k1 -> k2) -> Term dtk k1 -> Term dtk k2

type V0 = Var SZ
type V1 = Var (SS SZ)
type V2 = Var (SS (SS SZ))

data Field (dtk :: Kind) where
  Explicit :: Term dtk Type       -> Field dtk
  Implicit :: Term dtk Constraint -> Field dtk

type Branch   dtk = [Field  dtk]
type DataType dtk = [Branch dtk]

-- INTERPRETATION
-- ==============

  -- LoT == List of Types
infixr 5 :&&:
data LoT (ks :: Kind) where
  LoT0   :: LoT Type
  (:&&:) :: k -> LoT ks -> LoT (k -> ks)

type family Ty (dtk :: Kind) (t :: Term dtk k)
               (fix :: dtk)  (tys :: LoT dtk) :: k where
  -- and so on and so forth
  Ty (k1 -> ks) (Var SZ) fix (t1 :&&: ts) = t1
  Ty (k1 -> k2 -> ks) (Var (SS SZ)) fix (t1 :&&: t2 :&&: ts) = t2
  -- and so on and so forth
  Ty dtk Rec       fix tys = fix
  Ty dtk (Kon t)   fix tys = t
  Ty dtk (f :@: x) fix tys = (Ty dtk f fix tys) (Ty dtk x fix tys)

type f :$: x = Kon f :@: x

data NP (dtk :: Kind) (fs :: [Field dtk])
        (fix :: dtk)  (tys :: LoT dtk) where
  NP0 :: NP dtk '[] fix tys
  NPE :: forall (dtk :: Kind) (tm :: Term dtk Type) fix tys fs
       . Ty dtk tm fix tys -> NP dtk fs fix tys -> NP dtk (Explicit tm ': fs) fix tys
  NPI :: forall (dtk :: Kind) (tm :: Term dtk Constraint) fix tys fs
       . Ty dtk tm fix tys => NP dtk fs fix tys -> NP dtk (Implicit tm ': fs) fix tys

infixr 5 :*:
pattern x :*:  xs = NPE x xs

data NS (dtk :: Kind) (dt :: DataType dtk)
        (fix :: dtk)  (tys :: LoT dtk) where
  H :: NP dtk b  fix tys -> NS dtk (b ': bs) fix tys
  T :: NS dtk bs fix tys -> NS dtk (b ': bs) fix tys

pattern B0 x = H x
pattern B1 x = T (H x)
pattern B2 x = T (T (H x))
pattern B3 x = T (T (T (H x)))

data family Fix' (dtk :: Kind) (dt :: DataType dtk) :: dtk
data instance Fix' Type dt
  = R0 (Fix Type dt LoT0)
data instance Fix' (k1 -> Type) dt a
  = R1 (Fix (k1 -> Type) dt (a :&&: LoT0))
data instance Fix' (k1 -> k2 -> Type) dt a b
  = R2 (Fix (k1 -> k2 -> Type) dt (a :&&: b :&&: LoT0))

newtype Fix dtk (dt :: DataType dtk) (tys :: LoT dtk)
  = Fix (NS dtk dt (Fix' dtk dt) tys)

type family Apply k (f :: k) (tys :: LoT k) :: Type where
  Apply Type      f LoT0        = f
  Apply (k -> ks) f (t :&&: ts) = Apply ks (f t) ts

data Proxy (a :: k) = Proxy

infixr 5 :&:
data SLoT k (ts :: LoT k) where
  SLoT0 :: SLoT Type LoT0
  (:&:) :: Proxy a -> SLoT ks as -> SLoT (k -> ks) (a :&&: as)

pattern SLoT1 a = a :&: SLoT0
pattern SLoT2 a b = a :&: b :&: SLoT0
pattern SLoT3 a b c = a :&: b :&: c :&: SLoT0

class UltimateGeneric k (f :: k) | f -> k where
  type Rep f :: DataType k

  to   :: SLoT k ts -> Proxy f -> Apply k f ts -> Fix k (Rep f) ts
  from :: SLoT k ts -> Proxy f -> Fix k (Rep f) ts -> Apply k f ts

class SSLoT k (ts :: LoT k) where
  sslot :: SLoT k ts
instance SSLoT Type LoT0 where
  sslot = SLoT0
instance SSLoT ks as => SSLoT (k -> ks) (a :&&: as) where
  sslot = Proxy :&: sslot

to' :: (UltimateGeneric k f, SSLoT k ts)
    => Proxy f -> Apply k f ts -> Fix k (Rep f) ts
to' = to sslot

from' :: (UltimateGeneric k f, SSLoT k ts)
      => Proxy f -> Fix k (Rep f) ts -> Apply k f ts
from' = from sslot

instance UltimateGeneric (* -> *) [] where
  type Rep [] = '[ '[ ], '[ Explicit V0, Explicit (Rec :@: V0) ] ]

  to s@(SLoT1 _) _ [] = Fix $ B0 $ NP0
  to s@(SLoT1 _) p (x : xs) = Fix $ B1 $ NPE @_ @V0 x $ R1 (to s p xs) :*: NP0

  from s@(SLoT1 _) _ (Fix (B0 NP0)) = []
  from s@(SLoT1 _) p (Fix (B1 (x :*: R1 xs :*: NP0))) = x : from s p xs

instance UltimateGeneric (* -> * -> *) Either where
  type Rep Either = '[ '[ Explicit V0 ], '[ Explicit V1 ] ]

  to (SLoT2 _ _) _ (Left  x) = Fix $ B0 $ NPE @_ @V0 x NP0
  to (SLoT2 _ _) _ (Right x) = Fix $ B1 $ NPE @_ @V1 x NP0

  from (SLoT2 _ _) _ (Fix (B0 (x :*: NP0))) = Left  x
  from (SLoT2 _ _) _ (Fix (B1 (x :*: NP0))) = Right x

data Eql a b where
  Refl :: Eql a a
       -- a ~ b => Eql a b 

instance UltimateGeneric (k -> k -> *) Eql where
  type Rep Eql = '[ '[ Implicit ((~) :$: V0 :@: V1) ] ]

  to   s@(SLoT2 _ _) _ Refl = Fix $ B0 $ NPI NP0
  from s@(SLoT2 _ _) _ (Fix (B0 (NPI NP0))) = Refl


{-
show :: UltimateGeneric (*) x => x -> String
show = undefined

size :: UltimateGeneric (*) x => x -> Int
-}