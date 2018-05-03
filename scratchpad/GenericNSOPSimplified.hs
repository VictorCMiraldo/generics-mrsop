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
  Pos n     Type       = TypeError (Text "Index not found")
  Pos Z     (x -> xs) = x
  Pos (S n) (x -> xs) = Pos n xs

data Term (dtk :: Kind) k where
  Var   :: SNat n -> Term dtk (Pos n dtk)
  Kon   :: k -> Term dtk k
  (:@:) :: Term dtk (k1 -> k2) -> Term dtk k1 -> Term dtk k2
  -- If we really want this
  -- Rec   :: Term dtk dtk

type V0 = Var SZ
type V1 = Var (SS SZ)
type V2 = Var (SS (SS SZ))

type Branch   dtk = [Term dtk Type]
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

type family Ty (dtk :: Kind) {- (r :: dtk) -} (tys :: LoT dtk) (t :: Term dtk k) :: k where
  -- and so on and so forth
  Ty (k1 -> ks) {- r -} (t1 :&&: ts) (Var SZ)  = t1
  Ty (k1 -> k2 -> ks) {- r -} (t1 :&&: t2 :&&: ts) (Var (SS SZ))  = t2
  -- and so on and so forth
  -- Ty dtk r tys Rec     = r
  Ty dtk {- r -} tys (Kon t) = t
  Ty dtk {- r -} tys (f :@: x) = (Ty dtk {- r -} tys f) (Ty dtk {- r -} tys x)

type f :$: x = Kon f :@: x

data NA (dtk :: Kind) :: {- dtk -> -} LoT dtk -> Term dtk Type -> * where
  T :: forall dtk t {- r -} tys. Ty dtk {- r -} tys t -> NA dtk {- r -} tys t

unT :: NA dtk {- r -} tys t -> Ty dtk {- r -} tys t
unT (T x) = x

type SOPn k (c :: DataType k) {- (r :: k) -} (tys :: LoT k) = NS (NP (NA k {- r -} tys)) c

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

  to   :: SLoT k ts -> Proxy f -> Apply k f ts -> SOPn k (Code f) {- f -} ts
  from :: SLoT k ts -> Proxy f -> SOPn k (Code f) {- f -} ts -> Apply k f ts

class SSLoT k (ts :: LoT k) where
  sslot :: SLoT k ts
instance SSLoT Type LoT0 where
  sslot = SLoT0
instance SSLoT ks as => SSLoT (k -> ks) (a :&&: as) where
  sslot = Proxy :&: sslot

to' :: (UltimateGeneric k f, SSLoT k ts)
    => Proxy f -> Apply k f ts -> SOPn k (Code f) {- f -} ts
to' = to sslot

from' :: (UltimateGeneric k f, SSLoT k ts)
      => Proxy f -> SOPn k (Code f) {- f -} ts -> Apply k f ts
from' = from sslot

instance UltimateGeneric (* -> *) [] where
  type Code [] = '[ '[ ], '[ V0, [] :$: V0 ] ]

  to s@(SLoT1 _) _ [] = B0 $ Nil
  to s@(SLoT1 _) p (x : xs) = B1 $ T @(* -> *) @V0 x :* T xs :* Nil

  from s@(SLoT1 _) _ (B0 Nil) = []
  from s@(SLoT1 _) p (B1 (T x :* T xs :* Nil)) = x : xs

  -- You can choose how much you want
instance UltimateGeneric * [a] where
  type Code [a] = '[ '[ ], '[ Kon a, [] :$: Kon a ] ]

  to SLoT0 _ []     = B0 Nil
  to SLoT0 _ (x:xs) = B1 $ T x :* T xs :* Nil

  from SLoT0 _ (B0 Nil) = []
  from SLoT0 _ (B1 (T x :* T xs :* Nil)) = x : xs

instance UltimateGeneric (* -> *) Maybe where
  type Code Maybe = '[ '[ ], '[ V0 ] ]

  to s@(SLoT1 _) _ Nothing  = B0 $ Nil
  to s@(SLoT1 _) p (Just x) = B1 $ T @_ @V0 x :* Nil

  from s@(SLoT1 _) _ (B0 Nil) = Nothing
  from s@(SLoT1 _) p (B1 (T x :* Nil)) = Just x

instance UltimateGeneric (* -> * -> *) Either where
  type Code Either = '[ '[ V0 ], '[ V1 ] ]

  to (SLoT2 _ _) _ (Left  x) = B0 $ T @_ @V0 x :* Nil
  to (SLoT2 _ _) _ (Right x) = B1 $ T @_ @V1 x :* Nil

  from (SLoT2 _ _) _ (B0 (T x :* Nil)) = Left  x
  from (SLoT2 _ _) _ (B1 (T x :* Nil)) = Right x

-- and other two for either

class FunctorField (t :: Term (* -> *) Type) where
  gfmapF :: (a -> b)
         -> NA (* -> *) {- f -} (a :&&: LoT0) t
         -> NA (* -> *) {- f -} (b :&&: LoT0) t

instance FunctorField V0 where
  gfmapF f (T x) = T (f x)
instance (Functor f, FunctorField x) => FunctorField (f :$: x) where
  gfmapF f (T x) = T (fmap (unT . gfmapF f . T @_ @x) x)
instance FunctorField (Kon t) where
  gfmapF f (T x) = T x

type family All2 c xs :: Constraint where
  All2 c '[] = ()
  All2 c (x ': xs) = (All c x, All2 c xs)

type family All c xs :: Constraint where
  All c '[] = ()
  All c (x ': xs) = (c x, All c xs)
  -- AllE c (Implicit x ': xs)

gfmap :: forall f a b
       . (UltimateGeneric (* -> *) f, All2 FunctorField (Code f))
      => (a -> b) -> f a -> f b
gfmap f = from (SLoT1 Proxy) (Proxy)
        . goS
        . to   (SLoT1 Proxy) (Proxy)
  where
    goS :: All2 FunctorField xs
        => NS (NP (NA (* -> *) (a :&&: LoT0))) xs
        -> NS (NP (NA (* -> *) (b :&&: LoT0))) xs
    goS (Here  x) = Here  (goP x)
    goS (There x) = There (goS x)

    goP :: All FunctorField xs
        => NP (NA (* -> *) (a :&&: LoT0)) xs
        -> NP (NA (* -> *) (b :&&: LoT0)) xs
    goP Nil         = Nil
    goP (T x :* xs) = gfmapF f (T x) :* goP xs

fmapList :: (a -> b) -> [a] -> [b]
fmapList = gfmap
fmapMaybe :: (a -> b) -> Maybe a -> Maybe b
fmapMaybe = gfmap