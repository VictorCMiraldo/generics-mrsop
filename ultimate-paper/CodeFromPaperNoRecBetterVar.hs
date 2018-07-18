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

{-
gkmap :: forall k (f :: k) (as :: LoT k) (bs :: LoT k)
       . (GenericNSOP k f, SSLoT k bs, AllE2 KFunctorT (Code f))
      => Mappings as bs -> ApplyT k f as -> ApplyT k f bs
gkmap f = to . goS . from
  where
    goS :: AllE2 KFunctorT xs
        => NS (NB k as) xs -> NS (NB k bs) xs
    goS (Here  x) = Here  (goB x)
    goS (There x) = There (goS x)

    goB :: AllB KFunctorT xs
        => NB k as xs -> NB k bs xs
    goB (Cr x) = Cr (goP x)

    goP :: AllE KFunctorT xs
        => NP (NA k as) xs -> NP (NA k bs) xs
    goP Nil         = Nil
    goP (E x :* xs) = E (kmapT AMNil f (AA0 x)) :* goP xs

data AtomMappings (args :: [Atom dtk Type]) where
  AMNil  :: AtomMappings '[]
  AMCons :: KFunctorT Type x '[]
         => AtomMappings xs -> AtomMappings (x ': xs)
-}

class KFunctorT (f :: Atom dtk k) where
  kmapT :: Mappings as bs
        -> Mappings rs ts
        -> AtomApplyT k f rs
        -> AtomApplyT k f ts

data AtomApplyT k (t :: Atom dtk k) (tys :: LoT k)  where
  AA0  :: Ty k tys t -> AtomApplyT Type 
  AArg :: { unAArg :: AtomApplyT dtk tys k (f :@: x) args }
       -> AtomApplyT dtk tys (Type -> k) f (x ': args)

{-
instance KFunctorT Type (Var VZ) '[] where
  kmapT AMNil (MCons f _) (AA0 x) = AA0 $ f x
instance (KFunctorT (Type -> k) f (x ': args), KFunctorT Type x '[])
         => KFunctorT k (f :@: x) args where
  kmapT atoms f x = unAArg $ kmapT (AMCons atoms) f (AArg x)
instance KFunctor k f => KFunctorT k (Kon f) args where
  kmapT atoms f x = undefined

{-
instance KFunctorField (Var VZ) where
  kmapF (MCons f _) (E x) = E (f x)
instance (Functor f, KFunctorField x) => KFunctorField (Kon f :@: x) where
  kmapF f (E x) = E (fmap (unE . kmapF f . E @_ @_ @x) x)
instance KFunctorField (Kon t) where
  kmapF f (E x) = E x
-}
-}