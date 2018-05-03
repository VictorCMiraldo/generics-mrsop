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
  Ty (k1 -> k2 -> k3 -> ks) (t1 :&&: t2 :&&: t3 :&&: ts) (Var (SS (SS SZ)))  = t3
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

data Tm t where
  AnInt :: Int -> Tm Int
  APair :: Tm a -> Tm b -> Tm (a, b)
        -- forall a b. t ~ (a, b). Tm a -> Tm b -> Tm c

deriving instance Show (Tm t)

instance UltimateGeneric (* -> *) Tm where
  type Code Tm 
    = '[ Constr '[ Implicit ((~) :$: Kon Int :@: V0), Explicit (Kon Int) ] 
       , Exists KK (Exists KK (Constr '[
           Implicit ((~) :$: V2 :@: ((,) :$: V0 :@: V1))
         , Explicit (Tm :$: V0), Explicit (Tm :$: V1)
         ]))
       ]

  to (SLoT1 _) _ (AnInt n) = B0 $ Cr $ I :* E n :* Nil
  to (SLoT1 _) _ (APair x y) = B1 $ Ex $ Ex $ Cr $ I :* E x :* E y :* Nil

  from (SLoT1 _) _ (B0 (Cr (I :* E n :* Nil))) = AnInt n
  from (SLoT1 _) _ (B1 (Ex (Ex (Cr (I :* E x :* E y :* Nil))))) = APair x y