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
  Kon   :: k -> Term dtk k
  (:@:) :: Term dtk (k1 -> k2) -> Term dtk k1 -> Term dtk k2
  -- If we really want this
  Rec   :: Term dtk dtk

type V0 = Var SZ
type V1 = Var (SS SZ)
type V2 = Var (SS (SS SZ))

data Field (dtk :: Kind) where
  Explicit :: Term dtk Type       -> Field dtk
  Implicit :: Term dtk Constraint -> Field dtk

type Branch   dtk = [Field  dtk]
type DataType dtk = [Branch dtk]

data NS :: (k -> *) -> [k] -> * where
  Here   :: f k      -> NS f (k ': ks)
  There  :: NS f ks  -> NS f (k ': ks)

pattern B0 x = Here x
pattern B1 x = There (Here x)
pattern B2 x = There (There (Here x))
pattern B3 x = There (There (There (Here x)))

infixr 5 :*
data NP :: (k -> *) -> [k] -> * where
  Nil  ::                    NP f '[]
  (:*) :: f x -> NP f xs ->  NP f (x ': xs)

  -- LoT == List of Types
infixr 5 :&&:
data LoT (ks :: Kind) where
  LoT0   :: LoT Type
  (:&&:) :: k -> LoT ks -> LoT (k -> ks)

type family Ty (dtk :: Kind) (r :: dtk) (tys :: LoT dtk) (t :: Term dtk k) :: k where
  -- and so on and so forth
  Ty (k1 -> ks) r (t1 :&&: ts) (Var SZ)  = t1
  Ty (k1 -> k2 -> ks) r (t1 :&&: t2 :&&: ts) (Var (SS SZ))  = t2
  -- and so on and so forth
  Ty dtk r tys Rec     = r
  Ty dtk r tys (Kon t) = t
  Ty dtk r tys (f :@: x) = (Ty dtk r tys f) (Ty dtk r tys x)

type f :$: x = Kon f :@: x

data NA (dtk :: Kind) :: dtk -> LoT dtk -> Field dtk -> * where
  E :: forall dtk t r tys. Ty dtk r tys t -> NA dtk r tys (Explicit t)
  I :: forall dtk t r tys. Ty dtk r tys t => NA dtk r tys (Implicit t)

unE :: NA dtk r tys (Explicit t) -> Ty dtk r tys t
unE (E x) = x

type SOPn k (c :: DataType k) (r :: k) (tys :: LoT k) = NS (NP (NA k r tys)) c

data family Fix' (rx :: Kind) (dt :: DataType rx) :: rx
data instance Fix' Type dt
  = R0 (Fix Type dt LoT0)
data instance Fix' (k1 -> Type) dt a
  = R1 (Fix (k1 -> Type) dt (a :&&: LoT0))
data instance Fix' (k1 -> k2 -> Type) dt a b
  = R2 (Fix (k1 -> k2 -> Type) dt (a :&&: b :&&: LoT0))

newtype Fix dtk (dt :: DataType dtk) (tys :: LoT dtk)
  = Fix (SOPn dtk dt (Fix' dtk dt) tys)

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
  type Code f :: DataType k

  to   :: SLoT k ts -> Proxy f -> Apply k f ts -> SOPn k (Code f) f ts
  from :: SLoT k ts -> Proxy f -> SOPn k (Code f) f ts -> Apply k f ts

class SSLoT k (ts :: LoT k) where
  sslot :: SLoT k ts
instance SSLoT Type LoT0 where
  sslot = SLoT0
instance SSLoT ks as => SSLoT (k -> ks) (a :&&: as) where
  sslot = Proxy :&: sslot

to' :: (UltimateGeneric k f, SSLoT k ts)
    => Proxy f -> Apply k f ts -> SOPn k (Code f) f ts
to' = to sslot

from' :: (UltimateGeneric k f, SSLoT k ts)
      => Proxy f -> SOPn k (Code f) f ts -> Apply k f ts
from' = from sslot

instance UltimateGeneric (* -> *) [] where
  type Code [] = '[ '[ ], '[ Explicit V0, Explicit (Rec :@: V0) ] ]

  to s@(SLoT1 _) _ [] = B0 $ Nil
  to s@(SLoT1 _) p (x : xs) = B1 $ E @_ @V0 x :* E xs :* Nil

  from s@(SLoT1 _) _ (B0 Nil) = []
  from s@(SLoT1 _) p (B1 (E x :* E xs :* Nil)) = x : xs

  -- You can choose how much you want
instance UltimateGeneric * [a] where
  type Code [a] = '[ '[ ], '[ Explicit (Kon a), Explicit ([] :$: Kon a) ] ]

  to SLoT0 _ []     = B0 Nil
  to SLoT0 _ (x:xs) = B1 $ E x :* E xs :* Nil

  from SLoT0 _ (B0 Nil) = []
  from SLoT0 _ (B1 (E x :* E xs :* Nil)) = x : xs

instance UltimateGeneric (* -> *) Maybe where
  type Code Maybe = '[ '[ ], '[ Explicit V0 ] ]

  to s@(SLoT1 _) _ Nothing  = B0 $ Nil
  to s@(SLoT1 _) p (Just x) = B1 $ E @_ @V0 x :* Nil

  from s@(SLoT1 _) _ (B0 Nil) = Nothing
  from s@(SLoT1 _) p (B1 (E x :* Nil)) = Just x

instance UltimateGeneric (* -> * -> *) Either where
  type Code Either = '[ '[ Explicit V0 ], '[ Explicit V1 ] ]

  to (SLoT2 _ _) _ (Left  x) = B0 $ E @_ @V0 x :* Nil
  to (SLoT2 _ _) _ (Right x) = B1 $ E @_ @V1 x :* Nil

  from (SLoT2 _ _) _ (B0 (E x :* Nil)) = Left  x
  from (SLoT2 _ _) _ (B1 (E x :* Nil)) = Right x

-- and other two for either

data Eql a b where
  Refl :: Eql a a
       -- a ~ b => Eql a b 

instance UltimateGeneric (k -> k -> *) Eql where
  type Code Eql = '[ '[ Implicit ((~) :$: V0 :@: V1) ] ]

  to   s@(SLoT2 _ _) _ Refl = B0 $ I :* Nil
  from s@(SLoT2 _ _) _ (B0 (I :* Nil)) = Refl


class FunctorField (r :: * -> *) (t :: Term (* -> *) Type) where
  gfmapF :: (a -> b)
         -> NA (* -> *) r (a :&&: LoT0) (Explicit t)
         -> NA (* -> *) r (b :&&: LoT0) (Explicit t)

instance FunctorField r V0 where
  gfmapF f (E x) = E (f x)
instance (Functor f, FunctorField r x) => FunctorField r (f :$: x) where
  gfmapF f (E x) = E (fmap (unE . gfmapF f . E @_ @x @r) x)
instance FunctorField r (Kon t) where
  gfmapF f (E x) = E x
instance (Functor r, FunctorField r x) => FunctorField r (Rec :@: x) where
  gfmapF f (E x) = E (fmap (unE . gfmapF f . E @_ @x @r) x)

type family AllE2 c xs :: Constraint where
  AllE2 c '[] = ()
  AllE2 c (x ': xs) = (AllE c x, AllE2 c xs)

type family AllE c xs :: Constraint where
  AllE c '[] = ()
  AllE c (Explicit x ': xs) = (c x, AllE c xs)
  -- AllE c (Implicit x ': xs)

gfmap :: forall f a b
       . (UltimateGeneric (* -> *) f, AllE2 (FunctorField f) (Code f))
      => (a -> b) -> f a -> f b
gfmap f = from (SLoT1 (Proxy :: Proxy b)) (Proxy :: Proxy f)
        . goS
        . to   (SLoT1 (Proxy :: Proxy a)) (Proxy :: Proxy f)
  where
    goS :: AllE2 (FunctorField f) xs
        => NS (NP (NA (* -> *) f (a :&&: LoT0))) xs
        -> NS (NP (NA (* -> *) f (b :&&: LoT0))) xs
    goS (Here  x) = Here  (goP x)
    goS (There x) = There (goS x)

    goP :: AllE (FunctorField f) xs
        => NP (NA (* -> *) f (a :&&: LoT0)) xs
        -> NP (NA (* -> *) f (b :&&: LoT0)) xs
    goP Nil         = Nil
    goP (E x :* xs) = gfmapF f (E x) :* goP xs

fmapList :: (a -> b) -> [a] -> [b]
fmapList = gfmap
fmapMaybe :: (a -> b) -> Maybe a -> Maybe b
fmapMaybe = gfmap