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

data Proxy (a :: k) = Proxy

<<<<<<< HEAD
type Rep dtk (c :: DataType dtk) (tys :: LoT dtk)
  = NS (NP (NA dtk tys)) c

data SOPn dtk (c :: DataType dtk) (tys :: LoT dtk) where
  SOPn :: (IsLoT dtk tys) => Rep dtk c tys -> SOPn dtk c tys

sopLoT :: SOPn dtk c tys -> SLoT dtk tys
sopLoT (SOPn _) = sslot

class IsLoT k (ts :: LoT k) where
  sslot :: SLoT k ts
instance IsLoT Type LoT0 where
  sslot = SLoT0
instance IsLoT ks as => IsLoT (k -> ks) (a :&&: as) where
  sslot = Proxy :&: sslot
=======
data ApplyT (k :: Kind) (f :: k) (tys :: LoT k) :: Type where
  A0  :: f                 -> ApplyT Type      f  LoT0
  Arg :: ApplyT k (f t) ts -> ApplyT (k' -> k) f (t :&&: ts)

type family Apply k (f :: k) (tys :: LoT k) :: Type where
  Apply Type      f LoT0        = f
  Apply (k -> ks) f (t :&&: ts) = Apply ks (f t) ts

ravel :: forall k f ts. SSLoT k ts => Proxy f -> Apply k f ts -> ApplyT k f ts
ravel = go (sslot @_ @ts)
  where go :: forall k f ts. SLoT k ts -> Proxy f -> Apply k f ts -> ApplyT k f ts
        go SLoT0      _ x = A0 x
        go (t :&: ts) _ x = Arg (go ts Proxy x)

unravel :: ApplyT k f ts -> Apply k f ts
unravel (A0 f)  = f
unravel (Arg f) = unravel f

data Proxy (a :: k) = Proxy
>>>>>>> agda-ultimate-generics

infixr 5 :&:
data SLoT k (ts :: LoT k) where
  SLoT0 :: SLoT Type LoT0
  (:&:) :: Proxy a -> SLoT ks as -> SLoT (k -> ks) (a :&&: as)


type family Apply k (f :: k) (tys :: LoT k) :: Type where
  Apply Type      f LoT0        = f
  Apply (k -> ks) f (t :&&: ts) = Apply ks (f t) ts


pattern SLoT1 a = a :&: SLoT0
pattern SLoT2 a b = a :&: b :&: SLoT0
pattern SLoT3 a b c = a :&: b :&: c :&: SLoT0

<<<<<<< HEAD
data ApplyT (dtk :: Kind) (f :: dtk) (tys :: LoT k) :: Type where
  A0  :: f                   -> ApplyT Type       f  LoT0
  Arg :: ApplyT dtk (f t) ts -> ApplyT (k -> dtk) f  (t :&&: ts)

class UltimateGeneric k (f :: k) | f -> k where
  type Code f :: DataType k

  to   :: ApplyT k f ts -> SOPn k (Code f) ts
  from :: SOPn k (Code f) ts -> ApplyT k f ts

mto :: forall dtk f ts . (UltimateGeneric dtk f , IsLoT dtk ts)
    => Proxy f -> Apply dtk f ts -> SOPn dtk (Code f) ts
mto p = to . go p (sslot :: SLoT dtk ts)
  where
    proxyApp :: forall f a . Proxy f -> Proxy a -> Proxy (f a)
    proxyApp _ _ = Proxy

    go :: forall dtk ts f . Proxy f -> SLoT dtk ts -> Apply dtk f ts -> ApplyT dtk f ts
    go p SLoT0      x = A0 x
    go p (t :&: ts) x = Arg (go (proxyApp p t) ts x)

apply :: ApplyT dtk f ts -> Apply dtk f ts
apply (A0 f) = f
apply (Arg f) = apply f
=======
class SSLoT k (ts :: LoT k) where
  sslot :: SLoT k ts
instance SSLoT Type LoT0 where
  sslot = SLoT0
instance SSLoT ks as => SSLoT (k -> ks) (a :&&: as) where
  sslot = Proxy :&: sslot

class UltimateGeneric k (f :: k) | f -> k where
  type Code f :: DataType k

  to   :: ApplyT k f ts -> SOPn k (Code f) {- f -} ts
  from :: SSLoT k ts => SOPn k (Code f) {- f -} ts -> ApplyT k f ts
>>>>>>> agda-ultimate-generics

instance UltimateGeneric (* -> *) [] where
  type Code [] = '[ '[ ], '[ V0, [] :$: V0 ] ]

<<<<<<< HEAD
  to (Arg (A0 []))       = SOPn $ Here Nil
  to (Arg (A0 (x : xs))) = SOPn $ There (Here (T x :* T xs :* Nil))

  from (SOPn xs) = case sopLoT (SOPn xs) of
    (a :&: SLoT0) -> case xs of
       Here Nil                          -> Arg (A0 [])           
       There (Here (T x :* T xs :* Nil)) -> Arg (A0 (x : xs))
=======
  to (Arg (A0 []))       = B0 $ Nil
  to (Arg (A0 (x : xs))) = B1 $ T @(* -> *) @V0 x :* T xs :* Nil

  from :: forall ts. SSLoT (* -> *) ts
       => SOPn (* -> *) (Code []) ts -> ApplyT (* -> *) [] ts
  from sop = case sslot @_ @ts of
    a :&: SLoT0 -> case sop of
      B0 Nil -> Arg $ A0 []
      B1 (T x :* T xs :* Nil) -> Arg $ A0 $ x : xs
>>>>>>> agda-ultimate-generics

instance UltimateGeneric * [a] where
  type Code [a] = '[ '[ ], '[ Kon a, [] :$: Kon a ] ]

<<<<<<< HEAD
  to (A0 [])        = SOPn $ Here Nil
  to (A0 (x : xs))  = SOPn $ There (Here (T x :* T xs :* Nil))

  from (SOPn xs) = case sopLoT (SOPn xs) of
    SLoT0 -> case xs of
      Here Nil                          -> A0 []
      There (Here (T x :* T xs :* Nil)) -> A0 (x : xs)

{-
  from SLoT0 _ (B0 Nil) = []
  from SLoT0 _ (B1 (T x :* T xs :* Nil)) = x : xs
-}

{-
  to s@(SLoT1 _) _ [] = B0 $ Nil
  to s@(SLoT1 _) p (x : xs) = B1 $ T @(* -> *) @V0 x :* T xs :* Nil

  from s@(SLoT1 _) _ (B0 Nil) = []
  from s@(SLoT1 _) p (B1 (T x :* T xs :* Nil)) = x : xs
-}
=======
  to (A0 [])     = B0 Nil
  to (A0 (x:xs)) = B1 $ T x :* T xs :* Nil

  from :: forall ts. SSLoT (*) ts
       => SOPn (*) (Code [a]) ts -> ApplyT (*) [a] ts
  from sop = case sslot @_ @ts of
    SLoT0 -> case sop of
      B0 Nil -> A0 []
      B1 (T x :* T xs :* Nil) -> A0 $ x : xs
>>>>>>> agda-ultimate-generics

{-
-}

{-
to' :: (UltimateGeneric k f, SSLoT k ts)
    => Proxy f -> Apply k f ts -> SOPn k (Code f) {- f -} ts
to' = to sslot

from' :: (UltimateGeneric k f, SSLoT k ts)
      => Proxy f -> SOPn k (Code f) {- f -} ts -> Apply k f ts
from' = from sslot
-}

{-
  -- You can choose how much you want
instance UltimateGeneric (* -> *) Maybe where
  type Code Maybe = '[ '[ ], '[ V0 ] ]

  to (Arg (A0 Nothing))  = B0 $ Nil
  to (Arg (A0 (Just x))) = B1 $ T @_ @V0 x :* Nil

  from :: forall ts. SSLoT (* -> *) ts
       => SOPn (* -> *) (Code Maybe) ts -> ApplyT (* -> *) Maybe ts
  from sop = case sslot @_ @ts of
    a :&: SLoT0 -> case sop of
      B0 Nil -> Arg $ A0 Nothing
      B1 (T x :* Nil) -> Arg $ A0 $ Just x

instance UltimateGeneric (* -> * -> *) Either where
  type Code Either = '[ '[ V0 ], '[ V1 ] ]

  to (Arg (Arg (A0 (Left x))))  = B0 $ T @_ @V0 x :* Nil
  to (Arg (Arg (A0 (Right x)))) = B1 $ T @_ @V1 x :* Nil

  from :: forall ts. SSLoT (* -> * -> *) ts
       => SOPn   (* -> * -> *) (Code Either) ts
       -> ApplyT (* -> * -> *) Either ts
  from sop = case sslot @_ @ts of
    a :&: b :&: SLoT0 -> case sop of
      B0 (T x :* Nil) -> Arg $ Arg $ A0 $ Left  x
      B1 (T x :* Nil) -> Arg $ Arg $ A0 $ Right x

-- and other two for either
-}

class FunctorField (t :: Term (* -> *) Type) where
  gfmapF :: (a -> b)
         -> NA (* -> *) {- f -} (a :&&: LoT0) t
         -> NA (* -> *) {- f -} (b :&&: LoT0) t

instance FunctorField V0 where
  gfmapF f (T x) = T (f x)
instance (Functor f, FunctorField x) => FunctorField (f :$: x) where
  gfmapF f (T k) = T (fmap (unT . gfmapF f . T @_ @_ @x) k)
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
<<<<<<< HEAD
gfmap f = apply
        . from
        . goRep
        . mto Proxy
=======
gfmap f = unravel . from
        . goS
        . to . ravel Proxy
>>>>>>> agda-ultimate-generics
  where
    goRep :: All2 FunctorField xs
          => SOPn (* -> *) xs (a :&&: LoT0)
          -> SOPn (* -> *) xs (b :&&: LoT0)
    goRep (SOPn x) = SOPn (goS x)

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

fmapList :: (a -> b) -> [a] -> [b]{-# language DataKinds #-}
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

data ApplyT (k :: Kind) (f :: k) (tys :: LoT k) :: Type where
  A0  :: f                 -> ApplyT Type      f  LoT0
  Arg :: ApplyT k (f t) ts -> ApplyT (k' -> k) f (t :&&: ts)

type family Apply k (f :: k) (tys :: LoT k) :: Type where
  Apply Type      f LoT0        = f
  Apply (k -> ks) f (t :&&: ts) = Apply ks (f t) ts

ravel :: forall k f ts. SSLoT k ts => Proxy f -> Apply k f ts -> ApplyT k f ts
ravel = go (sslot @_ @ts)
  where go :: forall k f ts. SLoT k ts -> Proxy f -> Apply k f ts -> ApplyT k f ts
        go SLoT0      _ x = A0 x
        go (t :&: ts) _ x = Arg (go ts Proxy x)

unravel :: ApplyT k f ts -> Apply k f ts
unravel (A0 f)  = f
unravel (Arg f) = unravel f

data Proxy (a :: k) = Proxy

infixr 5 :&:
data SLoT k (ts :: LoT k) where
  SLoT0 :: SLoT Type LoT0
  (:&:) :: Proxy a -> SLoT ks as -> SLoT (k -> ks) (a :&&: as)

pattern SLoT1 a = a :&: SLoT0
pattern SLoT2 a b = a :&: b :&: SLoT0
pattern SLoT3 a b c = a :&: b :&: c :&: SLoT0

class SSLoT k (ts :: LoT k) where
  sslot :: SLoT k ts
instance SSLoT Type LoT0 where
  sslot = SLoT0
instance SSLoT ks as => SSLoT (k -> ks) (a :&&: as) where
  sslot = Proxy :&: sslot

class UltimateGeneric k (f :: k) | f -> k where
  type Code f :: DataType k

  to   :: ApplyT k f ts -> SOPn k (Code f) {- f -} ts
  from :: SSLoT k ts => SOPn k (Code f) {- f -} ts -> ApplyT k f ts

instance UltimateGeneric (* -> *) [] where
  type Code [] = '[ '[ ], '[ V0, [] :$: V0 ] ]

  to (Arg (A0 []))       = B0 $ Nil
  to (Arg (A0 (x : xs))) = B1 $ T @(* -> *) @V0 x :* T xs :* Nil

  from :: forall ts. SSLoT (* -> *) ts
       => SOPn (* -> *) (Code []) ts -> ApplyT (* -> *) [] ts
  from sop = case sslot @_ @ts of
    a :&: SLoT0 -> case sop of
      B0 Nil -> Arg $ A0 []
      B1 (T x :* T xs :* Nil) -> Arg $ A0 $ x : xs

  -- You can choose how much you want
instance UltimateGeneric * [a] where
  type Code [a] = '[ '[ ], '[ Kon a, [] :$: Kon a ] ]

  to (A0 [])     = B0 Nil
  to (A0 (x:xs)) = B1 $ T x :* T xs :* Nil

  from :: forall ts. SSLoT (*) ts
       => SOPn (*) (Code [a]) ts -> ApplyT (*) [a] ts
  from sop = case sslot @_ @ts of
    SLoT0 -> case sop of
      B0 Nil -> A0 []
      B1 (T x :* T xs :* Nil) -> A0 $ x : xs

instance UltimateGeneric (* -> *) Maybe where
  type Code Maybe = '[ '[ ], '[ V0 ] ]

  to (Arg (A0 Nothing))  = B0 $ Nil
  to (Arg (A0 (Just x))) = B1 $ T @_ @V0 x :* Nil

  from :: forall ts. SSLoT (* -> *) ts
       => SOPn (* -> *) (Code Maybe) ts -> ApplyT (* -> *) Maybe ts
  from sop = case sslot @_ @ts of
    a :&: SLoT0 -> case sop of
      B0 Nil -> Arg $ A0 Nothing
      B1 (T x :* Nil) -> Arg $ A0 $ Just x

instance UltimateGeneric (* -> * -> *) Either where
  type Code Either = '[ '[ V0 ], '[ V1 ] ]

  to (Arg (Arg (A0 (Left x))))  = B0 $ T @_ @V0 x :* Nil
  to (Arg (Arg (A0 (Right x)))) = B1 $ T @_ @V1 x :* Nil

  from :: forall ts. SSLoT (* -> * -> *) ts
       => SOPn   (* -> * -> *) (Code Either) ts
       -> ApplyT (* -> * -> *) Either ts
  from sop = case sslot @_ @ts of
    a :&: b :&: SLoT0 -> case sop of
      B0 (T x :* Nil) -> Arg $ Arg $ A0 $ Left  x
      B1 (T x :* Nil) -> Arg $ Arg $ A0 $ Right x

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
gfmap f = unravel . from
        . goS
        . to . ravel Proxy
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
fmapList = gfmap

{-
fmapMaybe :: (a -> b) -> Maybe a -> Maybe b
fmapMaybe = gfmap
-}
