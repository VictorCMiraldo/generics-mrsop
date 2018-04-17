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
{-# language FlexibleContexts #-}
{-# language ScopedTypeVariables #-}
module UltimateMultiRec where

import Data.Kind (type (*), type Type)
import GHC.Exts (Constraint)
import GHC.TypeLits (TypeError, ErrorMessage(..))

type Kind = (*)

data Nat = Z | S Nat

data SNat (n :: Nat) where
  SZ :: SNat Z
  SS :: SNat n -> SNat (S n)

class SSNat (n :: Nat) where
  ssnat :: SNat n
instance SSNat Z where
  ssnat = SZ
instance SSNat n => SSNat (S n) where
  ssnat = SS ssnat

type family Lookup (ix :: Nat) (xs :: [k]) :: k where
  Lookup Z     (x ': xs) = x
  Lookup (S n) (x ': xs) = Lookup n xs

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
  Rec   :: SNat n -> Term dtk dtk
  Kon   :: k -> Term dtk k
  (:@:) :: Term dtk (k1 -> k2) -> Term dtk k1 -> Term dtk k2

type V0 = Var SZ
type V1 = Var (SS SZ)
type V2 = Var (SS (SS SZ))

type R0 = Rec SZ
type R1 = Rec (SS SZ)
type R2 = Rec (SS (SS SZ))

data Field (dtk :: Kind) where
  Explicit :: Term dtk Type       -> Field dtk
  Implicit :: Term dtk Constraint -> Field dtk

type Branch   dtk = [Field    dtk]
type DataType dtk = [Branch   dtk]
type Family   dtk = [DataType dtk]

-- INTERPRETATION
-- ==============

  -- LoT == List of Types
infixr 5 :&&:
data LoT (ks :: Kind) where
  LoT0   :: LoT Type
  (:&&:) :: k -> LoT ks -> LoT (k -> ks)

type family Ty (dtk :: Kind) (t :: Term dtk k)
               (fix :: [dtk])  (tys :: LoT dtk) :: k where
  -- and so on and so forth
  Ty (k1 -> ks) (Var SZ) fix (t1 :&&: ts) = t1
  Ty (k1 -> k2 -> ks) (Var (SS SZ)) fix (t1 :&&: t2 :&&: ts) = t2
  -- and so on and so forth
  Ty dtk (Rec SZ) (f1 ': fs) tys = f1
  Ty dtk (Rec (SS SZ)) (f1 ': f2 ': fs) tys = f2
  -- and so on and so forth
  Ty dtk (Kon t)   fix tys = t
  Ty dtk (f :@: x) fix tys = (Ty dtk f fix tys) (Ty dtk x fix tys)

type f :$: x = Kon f :@: x

data NP (dtk :: Kind) (fs :: [Field dtk])
        (fix :: [dtk])  (tys :: LoT dtk) where
  NP0 :: NP dtk '[] fix tys
  NPE :: forall (dtk :: Kind) (tm :: Term dtk Type) fix tys fs
       . Ty dtk tm fix tys -> NP dtk fs fix tys -> NP dtk (Explicit tm ': fs) fix tys
  NPI :: forall (dtk :: Kind) (tm :: Term dtk Constraint) fix tys fs
       . Ty dtk tm fix tys => NP dtk fs fix tys -> NP dtk (Implicit tm ': fs) fix tys

infixr 5 :*:
pattern x :*:  xs = NPE x xs

data NS (dtk :: Kind) (dt :: DataType dtk)
        (fix :: [dtk])  (tys :: LoT dtk) where
  H :: NP dtk b  fix tys -> NS dtk (b ': bs) fix tys
  T :: NS dtk bs fix tys -> NS dtk (b ': bs) fix tys

pattern B0 x = H x
pattern B1 x = T (H x)
pattern B2 x = T (T (H x))
pattern B3 x = T (T (T (H x)))

data family Fix' (dtk :: Kind) (fam :: Family dtk) (ix :: Nat) :: dtk
data instance Fix' Type fam ix
  = R0 (Fix Type fam ix LoT0)
data instance Fix' (k1 -> Type) fam ix a
  = R1 (Fix (k1 -> Type) fam ix (a :&&: LoT0))
data instance Fix' (k1 -> k2 -> Type) fam ix a b
  = R2 (Fix (k1 -> k2 -> Type) fam ix (a :&&: b :&&: LoT0))

type family Fixs' (dtk :: Kind) (fam :: Family dtk) (dt :: Family dtk) (n :: Nat) :: [dtk] where
  Fixs' dtk fam '[]       n = '[]
  Fixs' dtk fam (x ': xs) n = Fix' dtk fam n ': Fixs' dtk fam xs (S n)

type Fixs dtk (fam :: Family dtk) = Fixs' dtk fam fam Z

newtype Fix dtk (fam :: Family dtk) (ix :: Nat) (tys :: LoT dtk)
  = Fix (NS dtk (Lookup ix fam) (Fixs dtk fam) tys)

type family Apply k (fs :: k) (tys :: LoT k) :: Type where
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

class UltimateGeneric k (fs :: [k]) | fs -> k where
  type Rep fs :: Family k

  to   :: SLoT k ts -> Proxy fs -> SNat ix -> Apply k (Lookup ix fs) ts -> Fix k (Rep fs) ix ts
  from :: SLoT k ts -> Proxy fs -> SNat ix -> Fix k (Rep fs) ix ts -> Apply k (Lookup ix fs) ts

type family IxOf (xs :: [k]) (x :: k) :: Nat where
  IxOf (x ': xs) x = Z
  IxOf (y ': xs) x = S (IxOf xs x)

class UltimateGeneric k fs => UltimateGeneric' k (fs :: [k]) f | f -> fs k where

class SSLoT k (ts :: LoT k) where
  sslot :: SLoT k ts
instance SSLoT Type LoT0 where
  sslot = SLoT0
instance SSLoT ks as => SSLoT (k -> ks) (a :&&: as) where
  sslot = Proxy :&: sslot

to' :: (UltimateGeneric k fs, SSLoT k ts)
    => Proxy fs -> SNat ix -> Apply k (Lookup ix fs) ts -> Fix k (Rep fs) ix ts
to' = to sslot

from' :: (UltimateGeneric k fs, SSLoT k ts)
      => Proxy fs -> SNat ix -> Fix k (Rep fs) ix ts -> Apply k (Lookup ix fs) ts
from' = from sslot

to_ :: forall k (fs :: [k]) (f :: k) (ts :: LoT k)
     . (UltimateGeneric' k fs f, SSLoT k ts,
        SSNat (IxOf fs f), Lookup (IxOf fs f) fs ~ f)
    => Proxy f -> Apply k f ts -> Fix k (Rep fs) (IxOf fs f) ts
to_ _ = to sslot (Proxy :: Proxy fs) ssnat

instance UltimateGeneric (* -> *) '[ [] ] where
  type Rep '[ [] ] = '[ '[ '[ ], '[ Explicit V0, Explicit (R0 :@: V0) ] ] ]

  to s@(SLoT1 _) _ SZ [] = Fix $ B0 $ NP0
  to s@(SLoT1 _) p SZ (x : xs) = Fix $ B1 $ NPE @_ @V0 x $ R1 (to s p SZ xs) :*: NP0

  from s@(SLoT1 _) _ SZ (Fix (B0 NP0)) = []
  from s@(SLoT1 _) p SZ (Fix (B1 (x :*: R1 xs :*: NP0))) = x : from s p SZ xs

instance UltimateGeneric (* -> * -> *) '[ Either ] where
  type Rep '[ Either ] = '[ '[ '[ Explicit V0 ], '[ Explicit V1 ] ] ]

  to (SLoT2 _ _) _ SZ (Left  x) = Fix $ B0 $ NPE @_ @V0 x NP0
  to (SLoT2 _ _) _ SZ (Right x) = Fix $ B1 $ NPE @_ @V1 x NP0

  from (SLoT2 _ _) _ SZ (Fix (B0 (x :*: NP0))) = Left  x
  from (SLoT2 _ _) _ SZ (Fix (B1 (x :*: NP0))) = Right x

data Eql a b where
  Refl :: Eql a a
       -- a ~ b => Eql a b 

instance UltimateGeneric (k -> k -> *) '[ Eql ] where
  type Rep '[ Eql ] = '[ '[ '[ Implicit ((~) :$: V0 :@: V1) ] ] ]

  to   s@(SLoT2 _ _) _ SZ Refl = Fix $ B0 $ NPI NP0
  from s@(SLoT2 _ _) _ SZ (Fix (B0 (NPI NP0))) = Refl

data Mongi a b = Mongi a (Pongi b a)
data Pongi a b = Pongi a (Mongi a b) | Done

type MongiPongi = '[ Mongi, Pongi ]

instance UltimateGeneric (* -> * -> *) '[ Mongi, Pongi ] where
  type Rep '[ Mongi, Pongi ] = '[ 
      '[ '[ Explicit V0, Explicit (R1 :@: V1 :@: V0) ] ]
    , '[ '[ Explicit V0, Explicit (R0 :@: V0 :@: V1) ], '[ ] ]
    ]
  
  to s@(SLoT2 a b) p SZ      (Mongi x xs)
    = Fix $ B0 $ NPE @_ @V0 x $ R2 (to (SLoT2 b a) p (SS SZ) xs) :*: NP0
  to s@(SLoT2 a b) p (SS SZ) (Pongi y ys)
    = Fix $ B0 $ NPE @_ @V0 y $ R2 (to (SLoT2 a b) p SZ ys) :*: NP0
  to s@(SLoT2 a b) p (SS SZ) Done
    = Fix $ B1 $ NP0

instance UltimateGeneric' (* -> * -> *) MongiPongi Mongi
instance UltimateGeneric' (* -> * -> *) MongiPongi Pongi

{-
show :: UltimateGeneric (*) x => x -> String
show = undefined

size :: UltimateGeneric (*) x => x -> Int
-}