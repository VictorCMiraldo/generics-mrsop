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
{-# language UndecidableInstances #-}
module CodeFromPaper where

import Data.Kind (type (*), type Type, Constraint)

type Kind = (*)

data TyVar (dtk :: Kind) k where
  VZ :: TyVar (x -> xs) x
  VS :: TyVar xs k -> TyVar (x -> xs) k

data Atom (dtk :: Kind) k where
  Var    :: TyVar dtk k -> Atom dtk k
  Kon    :: k           -> Atom dtk k
  (:@:)  :: Atom dtk (k1 -> k2) -> Atom dtk k1 -> Atom dtk k2

type V0  = Var VZ
type V1  = Var (VS VZ)
type V2  = Var (VS (VS VZ))

infixr 5 :&&:
data LoT (dtk :: Kind) where
  LoT0    ::                  LoT (*)
  (:&&:)  :: k -> LoT ks ->   LoT (k -> ks)

type family Ty (dtk :: Kind) (tys :: LoT dtk) (t :: Atom dtk k) :: k where
  Ty (k -> ks) (t :&&: ts) (Var VZ)     = t
  Ty (k -> ks) (t :&&: ts) (Var (VS v)) = Ty ks ts (Var v)
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
  E ::  forall dtk t tys .  { unE :: Ty dtk tys t }  ->  NA dtk tys (Explicit t)
  I ::  forall dtk t tys .  Ty dtk tys t  =>  NA dtk tys (Implicit t)

infixr 5 :*
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

instance GenericNSOP (* -> *) [] where
  type Code [] = '[ Constr '[ ], Constr '[ Explicit V0, Explicit (Kon [] :@: V0) ] ]

  from (Arg (A0 [])) = Here $ Cr $ Nil
  from (Arg (A0 (x : xs))) = There $ Here $ Cr $ E x :* E xs :* Nil
  
  to :: forall tys. SSLoT (* -> *) tys
     => SOPn (* -> *) (Code []) tys -> ApplyT (* -> *) [] tys
  to sop = case sslot @(* -> *) @tys of
    SLoTA SLoT0 -> case sop of
      Here (Cr Nil) -> Arg $ A0 []
      There (Here (Cr (E x :* E xs :* Nil))) -> Arg $ A0 $ x : xs


-- Try multi-arity map

type family AllE2 c xs :: Constraint where
  AllE2 c '[] = ()
  AllE2 c (x ': xs) = (AllB c x, AllE2 c xs)

type family AllB c xs :: Constraint where
  AllB c (Constr x) = AllE c x

type family AllE c xs :: Constraint where
  AllE c '[] = ()
  AllE c (Explicit x ': xs) = (c x, AllE c xs)


data Mappings (as :: LoT dtk) (bs :: LoT dtk) where
  MNil  :: Mappings LoT0 LoT0
  MCons :: (a -> b) -> Mappings as bs -> Mappings (a :&&: as) (b :&&: bs)

data Proxy (a :: k) = Proxy

class KFunctor k (f :: k) where
  kmap :: Mappings as bs -> ApplyT k f as -> ApplyT k f bs

gkmap :: forall k (f :: k) (as :: LoT k) (bs :: LoT k)
       . (GenericNSOP k f, SSLoT k bs, AllE2 KFunctorField (Code f))
      => Mappings as bs -> ApplyT k f as -> ApplyT k f bs
gkmap f = to . goS . from
  where
    goS :: AllE2 KFunctorField xs
        => NS (NB k as) xs -> NS (NB k bs) xs
    goS (Here  x) = Here  (goB x)
    goS (There x) = There (goS x)

    goB :: AllB KFunctorField xs
        => NB k as xs -> NB k bs xs
    goB (Cr x) = Cr (goP x)

    goP :: AllE KFunctorField xs
        => NP (NA k as) xs -> NP (NA k bs) xs
    goP Nil         = Nil
    goP (E x :* xs) = kmapf f (E x) :* goP xs

class KFunctorField (t :: Atom dtk Type) where
  kmapf :: Mappings as bs
        -> NA dtk as (Explicit t)
        -> NA dtk bs (Explicit t)

data STyVar k (t :: TyVar k Type) where
  SVZ :: STyVar (Type -> k) VZ
  SVS :: STyVar k v -> STyVar (Type -> k) (VS v)

class SForTyVar k (t :: TyVar k Type) where
  styvar :: STyVar k t
instance SForTyVar (Type -> k) VZ where
  styvar = SVZ
instance SForTyVar k v => SForTyVar (Type -> k) (VS v) where
  styvar = SVS styvar

instance forall k (v :: TyVar k Type). SForTyVar k v => KFunctorField (Var v) where
  kmapf :: forall dtk (as :: LoT dtk) (bs :: LoT dtk) v.
           SForTyVar dtk v 
        => Mappings as bs
        -> NA dtk as (Explicit (Var v))
        -> NA dtk bs (Explicit (Var v))
  kmapf f (E x) = E (go (styvar @dtk @v) f x)
    where go :: forall k (as :: LoT k) (bs :: LoT k) (v :: TyVar k Type)
              . STyVar k v
             -> Mappings as bs
             -> Ty k as (Var v)
             -> Ty k bs (Var v)
          go SVZ      (MCons g _)  x = g x
          go (SVS v') (MCons _ f') x = go v' f' x

instance KFunctorField (Kon t) where
  kmapf f (E x) = E x

instance (KFunctorHead f, KFunctorField x) => KFunctorField (f :@: x) where
  kmapf :: forall dtk (as :: LoT dtk) (bs :: LoT dtk)
                  (f :: Atom dtk (Type -> Type)) (x :: Atom dtk Type).
           (KFunctorHead f, KFunctorField x)
        => Mappings as bs
        -> NA dtk as (Explicit (f :@: x))
        -> NA dtk bs (Explicit (f :@: x))
  kmapf f (E x) = E
                $ unA0 $ unArg
                $ kmaph (Proxy :: Proxy f) f
                        (MCons (unE . kmapf f . E @_ @x) MNil)
                $ Arg $ A0 x

class KFunctorHead (t :: Atom dtk k) where
  kmaph :: Proxy t
        -> Mappings as bs
        -> Mappings rs ts
        -> ApplyT k (Ty dtk as t) rs
        -> ApplyT k (Ty dtk bs t) ts

instance (KFunctorHead f, KFunctorField x) => KFunctorHead (f :@: x) where
  kmaph :: forall dtk (as :: LoT dtk) (bs :: LoT dtk)
                  k (rs :: LoT k) (ts :: LoT k)
                  (f :: Atom dtk (Type -> k)) (x :: Atom dtk Type).
           (KFunctorHead f, KFunctorField x)
        => Proxy (f :@: x) -> Mappings as bs
        -> Mappings rs ts
        -> ApplyT k (Ty dtk as (f :@: x)) rs
        -> ApplyT k (Ty dtk bs (f :@: x)) ts
  kmaph _ f r x = unArg
                $ kmaph (Proxy :: Proxy f) f
                        (MCons (unE . kmapf f . E @_ @x) r)
                $ Arg x