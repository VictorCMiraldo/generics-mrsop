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
{-# language StandaloneDeriving #-}
module Generic1SOP where

import Data.Kind (type (*), type Type, Constraint)
import Type.Reflection (TypeRep)

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
  -- Rec   :: Term dtk dtk

type f :$: x = Kon f :@: x

type V0 = Var SZ
type V1 = Var (SS SZ)
type V2 = Var (SS (SS SZ))

data Field (dtk :: Kind) where
  Explicit :: Term dtk Type       -> Field dtk
  Implicit :: Term dtk Constraint -> Field dtk

data SKind (k :: *) = KK

data Branch (dtk :: Kind) where
  Exists :: SKind k -> Branch (k -> dtk) -> Branch dtk
  Constr :: [Field dtk] -> Branch dtk 

type DataType dtk = [Branch dtk]

  -- LoT == List of Types
infixr 5 :&&:
data LoT (ks :: Kind) where
  LoT0   :: LoT Type
  (:&&:) :: k -> LoT ks -> LoT (k -> ks)

data NS (dtk :: Kind) :: LoT dtk -> DataType dtk -> * where
  Here  :: NE dtk tys b  -> NS dtk tys (b ': bs)
  There :: NS dtk tys bs -> NS dtk tys (b ': bs)

pattern B0 x = Here x
pattern B1 x = There (Here x)
pattern B2 x = There (There (Here x))
pattern B3 x = There (There (There (Here x)))

data NE (dtk :: Kind) :: LoT dtk -> Branch dtk -> * where
  Ex :: forall k (t :: k) (p :: SKind k) dtk tys r. 
        NE (k -> dtk) (t :&&: tys) r -> NE dtk tys (Exists p r)
  Cr :: NP dtk tys fs -> NE dtk tys (Constr fs)

infixr 5 :*
data NP (dtk :: Kind) :: LoT dtk -> [Field dtk] -> * where
  Nil  ::                                   NP dtk tys '[]
  (:*) :: NA dtk tys x -> NP dtk tys xs ->  NP dtk tys (x ': xs)

type family Ty (dtk :: Kind) (tys :: LoT dtk) (t :: Term dtk k) :: k where
  -- and so on and so forth
  Ty (k1 -> ks) (t1 :&&: ts) (Var SZ)  = t1
  Ty (k1 -> k2 -> ks) (t1 :&&: t2 :&&: ts) (Var (SS SZ))  = t2
  -- and so on and so forth
  Ty dtk tys (Kon t) = t
  Ty dtk tys (f :@: x) = (Ty dtk tys f) (Ty dtk tys x)

data NA (dtk :: Kind) :: LoT dtk -> Field dtk -> * where
  E :: forall dtk t tys. Ty dtk tys t -> NA dtk tys (Explicit t)
  I :: forall dtk t tys. Ty dtk tys t => NA dtk tys (Implicit t)

unE :: NA dtk tys (Explicit t) -> Ty dtk tys t
unE (E x) = x

type SOPn k (c :: DataType k) (tys :: LoT k) = NS k tys c

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

  to   :: SLoT k ts -> Proxy f -> Apply k f ts -> SOPn k (Code f) ts
  from :: SLoT k ts -> Proxy f -> SOPn k (Code f) ts -> Apply k f ts

instance UltimateGeneric (* -> *) [] where
  type Code [] = '[ Constr '[ ], Constr '[ Explicit V0, Explicit ([] :$: V0) ] ]

  to s@(SLoT1 _) _ [] = B0 $ Cr $ Nil
  to s@(SLoT1 _) p (x : xs) = B1 $ Cr $ E @_ @V0 x :* E xs :* Nil

  from s@(SLoT1 _) _ (B0 (Cr Nil)) = []
  from s@(SLoT1 _) p (B1 (Cr (E x :* E xs :* Nil))) = x : xs

data Showable where
  Showable :: Show t => t -> Showable

instance UltimateGeneric (*) Showable where
  type Code Showable = '[ Exists KK (Constr '[ Implicit (Show :$: V0), Explicit V0 ]) ]

  to   SLoT0 _ (Showable x) = B0 $ Ex $ Cr $ I :* E @_ @V0 x :* Nil
  from SLoT0 _ (B0 (Ex (Cr (I :* E x :* Nil)))) = Showable x

{-
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


class FunctorField (t :: Term (* -> *) Type) where
  gfmapF :: (a -> b)
         -> NA (* -> *) {- f -} (a :&&: LoT0) (Explicit t)
         -> NA (* -> *) {- f -} (b :&&: LoT0) (Explicit t)

instance FunctorField V0 where
  gfmapF f (E x) = E (f x)
instance (Functor f, FunctorField x) => FunctorField (f :$: x) where
  gfmapF f (E x) = E (fmap (unE . gfmapF f . E @_ @x) x)
instance FunctorField (Kon t) where
  gfmapF f (E x) = E x

type family AllE2 c xs :: Constraint where
  AllE2 c '[] = ()
  AllE2 c (x ': xs) = (AllE c x, AllE2 c xs)

type family AllE c xs :: Constraint where
  AllE c '[] = ()
  AllE c (Explicit x ': xs) = (c x, AllE c xs)
  -- AllE c (Implicit x ': xs)

gfmap :: forall f a b
       . (UltimateGeneric (* -> *) f, AllE2 FunctorField (Code f))
      => (a -> b) -> f a -> f b
gfmap f = from (SLoT1 (Proxy :: Proxy b)) (Proxy :: Proxy f)
        . goS
        . to   (SLoT1 (Proxy :: Proxy a)) (Proxy :: Proxy f)
  where
    goS :: AllE2 FunctorField xs
        => NS (NP (NA (* -> *) (a :&&: LoT0))) xs
        -> NS (NP (NA (* -> *) (b :&&: LoT0))) xs
    goS (Here  x) = Here  (goP x)
    goS (There x) = There (goS x)

    goP :: AllE FunctorField xs
        => NP (NA (* -> *) (a :&&: LoT0)) xs
        -> NP (NA (* -> *) (b :&&: LoT0)) xs
    goP Nil         = Nil
    goP (E x :* xs) = gfmapF f (E x) :* goP xs

fmapList :: (a -> b) -> [a] -> [b]
fmapList = gfmap
fmapMaybe :: (a -> b) -> Maybe a -> Maybe b
fmapMaybe = gfmap
-}