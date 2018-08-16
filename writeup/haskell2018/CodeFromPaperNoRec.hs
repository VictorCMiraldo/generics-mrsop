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
{-# language RankNTypes #-}
module CodeFromPaper where

import Data.Kind (type (*), type Type, Constraint)

type Kind = (*)

data Nat = Z | S Nat

data SNat (n :: Nat) where
  SZ :: SNat Z
  SS :: SNat n -> SNat (S n)

data Atom (dtk :: Kind) k where
  Var    :: SNat n  -> Atom dtk (Pos n dtk)
  Kon    :: k       -> Atom dtk k
  (:@:)  :: Atom dtk (k1 -> k2) -> Atom dtk k1 -> Atom dtk k2

type V0  = Var SZ
type V1  = Var (SS SZ)
type V2  = Var (SS (SS SZ))

type family Pos (n :: Nat) (dtk :: Kind) :: Kind where
  -- Pos n      Type       = TypeError (Text "Not found")
  Pos Z      (x -> xs)  = x
  Pos (S n)  (x -> xs)  = Pos n xs

infixr 5 :&&:
data LoT (dtk :: Kind) where
  LoT0    ::                  LoT (*)
  (:&&:)  :: k -> LoT ks ->   LoT (k -> ks)

type family Ty (dtk :: Kind) (tys :: LoT dtk) (t :: Atom dtk k) :: k where
  Ty (k1       -> ks) (t1         :&&: ts) V0  = t1
  Ty (k1 -> k2 -> ks) (t1 :&&: t2 :&&: ts) V1  = t2
  Ty dtk tys (Kon t)   = t
  Ty dtk tys (f :@: x) = (Ty dtk tys f) (Ty dtk tys x)

data Field (dtk :: Kind) where
  Explicit  :: Atom dtk (*)         -> Field dtk
  Implicit  :: Atom dtk Constraint  -> Field dtk

data SKind (ell :: Kind) = KK

data Branch (dtk :: Kind) where
  Exists  :: SKind ell -> Branch (ell -> dtk)   -> Branch dtk
  Constr  :: [Field dtk]                        -> Branch dtk

type DataType dtk = [Branch dtk]

data NA (dtk :: Kind) :: LoT dtk -> Field dtk -> * where
  E ::  forall dtk t tys .  Ty dtk tys t  ->  NA dtk tys (Explicit t)
  I ::  forall dtk t tys .  Ty dtk tys t  =>  NA dtk tys (Implicit t)

data NP :: (k -> *) -> [k] -> * where
  Nil  ::                    NP f '[]
  (:*) :: f x -> NP f xs ->  NP f (x ': xs)

data NB (dtk :: Kind) :: LoT dtk -> Branch dtk -> * where
  Ex  ::  forall ell (t :: ell) (p :: SKind ell) dtk tys c .
          NB (ell -> dtk) (t :&&: tys) c  -> NB dtk tys (Exists p c)
  Cr  ::  NP (NA dtk tys) fs              -> NB dtk tys (Constr fs)

data NS :: (k -> *) -> [k] -> * where
  Here   :: f k      -> NS f (k ': ks)
  There  :: NS f ks  -> NS f (k ': ks)

type SOPn dtk (c :: DataType dtk) (tys :: LoT dtk) = NS (NB dtk tys) c

data SLoT dtk (tys :: LoT dtk) where
  SLoT0  ::                 SLoT (*)     LoT0
  SLoTA  ::  SLoT ks ts ->  SLoT (k -> ks)  (t :&&: ts)

class SSLoT k (tys :: LoT k) where
  sslot :: SLoT k tys
instance SSLoT (*) LoT0 where
  sslot = SLoT0
instance SSLoT ks ts => SSLoT (k -> ks) (t :&&: ts) where
  sslot = SLoTA sslot

data ApplyT k (f :: k) (tys :: LoT k) :: * where
  A0   :: { unA0   ::  f  }  -> ApplyT (*)     f  LoT0
  Arg  :: { unArg  ::  ApplyT ks (f t) ts  }
                             -> ApplyT (k -> ks)  f (t :&&: ts)

class GenericNSOP dtk (f :: dtk) where
  type Code f :: DataType dtk
  from  ::  ApplyT dtk f tys -> SOPn dtk (Code f) tys
  to    ::  SSLoT dtk tys
        =>  SOPn dtk (Code f) tys -> ApplyT dtk f tys

type family Apply dtk (f :: dtk) (tys :: LoT dtk) :: (*) where
  Apply (*)       f LoT0         = f
  Apply (k -> ks) f (t :&&: ts)  = Apply ks (f t) ts

unravel :: ApplyT k f ts -> Apply k f ts
unravel (A0   x) = x
unravel (Arg  x) = unravel x

ravel  ::  forall k f ts . SSLoT k ts 
       =>  Apply k f ts -> ApplyT k f ts
ravel = go (sslot @_ @ts)
  where
    go  ::  forall k f ts . SLoT k ts
        ->  Apply k f ts -> ApplyT k f ts
    go SLoT0       x = A0   x
    go (SLoTA ts)  x = Arg  (go ts x)