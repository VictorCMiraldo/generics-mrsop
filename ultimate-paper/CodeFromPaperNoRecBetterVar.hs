{-# language DataKinds #-}
{-# language ConstraintKinds #-}
{-# language ExplicitNamespaces #-}
{-# language TypeOperators #-}
{-# language GADTs #-}
{-# language TypeFamilies #-}
{-# language InstanceSigs #-}
{-# language TypeApplications #-}
{-# language FlexibleInstances #-}
{-# language MultiParamTypeClasses #-}
{-# language TypeInType #-}
{-# language ScopedTypeVariables #-}
{-# language FlexibleContexts #-}
{-# language DefaultSignatures #-}
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
  AllE c (Implicit x ': xs) = AllE c xs


type family ISatisfied dtk (tys :: LoT dtk) xs :: Constraint where
  ISatisfied dtk tys '[] = ()
  ISatisfied dtk tys (x ': xs) = (ISatisfiedB dtk tys x, ISatisfied dtk tys xs)

type family ISatisfiedB dtk (tys :: LoT dtk) xs :: Constraint where
  ISatisfiedB dtk tys (Constr x) = ISatisfiedE dtk tys x

type family ISatisfiedE dtk (tys :: LoT dtk) xs :: Constraint where
  ISatisfiedE dtk tys '[] = ()
  ISatisfiedE dtk tys (Implicit x ': xs) = (Ty dtk tys x, ISatisfiedE dtk tys xs)
  ISatisfiedE dtk tys (Explicit x ': xs) = ISatisfiedE dtk tys xs


data Mappings (as :: LoT dtk) (bs :: LoT dtk) where
  MNil  :: Mappings LoT0 LoT0
  MCons :: (a -> b) -> Mappings as bs -> Mappings (a :&&: as) (b :&&: bs)

data Proxy (a :: k) = Proxy

class KFunctor k (f :: k) where
  kmap :: SSLoT k bs => Mappings as bs -> ApplyT k f as -> ApplyT k f bs

  default kmap :: (GenericNSOP k f, SSLoT k bs,
                   AllE2 KFunctorField (Code f), ISatisfied k bs (Code f))
               => Mappings as bs -> ApplyT k f as -> ApplyT k f bs
  kmap fs = to . gkmap (Proxy :: Proxy f) fs . from

instance KFunctor (* -> *) []

listmap :: (a -> b) -> [a] -> [b]
listmap f x = unravel $ kmap (MCons f MNil) $ ravel x

data Showy t where
  Showable   :: Show t => t -> Showy t
  NoShowable :: String -> t -> Showy t

instance GenericNSOP (* -> *) Showy where
  type Code Showy = '[ Constr '[ Implicit (Kon Show :@: V0), Explicit V0 ] 
                     , Constr '[ Explicit (Kon String), Explicit V0] ]

  from (Arg (A0 (Showable x))) = Here $ Cr $ I :* E x :* Nil
  from (Arg (A0 (NoShowable s x))) = There $ Here $ Cr $ E s :* E x :* Nil

  to :: forall tys. SSLoT (* -> *) tys
     => SOPn (* -> *) (Code Showy) tys -> ApplyT (* -> *) Showy tys
  to sop = case sslot @(* -> *) @tys of
    SLoTA SLoT0 -> case sop of
      Here (Cr (I :* E x :* Nil)) -> Arg $ A0 $ Showable x
      There (Here (Cr (E s :* E x :* Nil))) -> Arg $ A0 $ NoShowable s x

showymap :: Show b => (a -> b) -> Showy a -> Showy b
showymap f x = unravel $ to
             $ gkmap (Proxy :: Proxy Showy) (MCons f MNil)
             $ from $ ravel x

gkmap :: forall k (f :: k) (as :: LoT k) (bs :: LoT k)
       . (GenericNSOP k f, AllE2 KFunctorField (Code f), ISatisfied k bs (Code f))
      => Proxy f -> Mappings as bs -> SOPn k (Code f) as -> SOPn k (Code f) bs
gkmap _ f = goS
  where
    goS :: (AllE2 KFunctorField xs, ISatisfied k bs xs)
        => NS (NB k as) xs -> NS (NB k bs) xs
    goS (Here  x) = Here  (goB x)
    goS (There x) = There (goS x)

    goB :: (AllB KFunctorField xs, ISatisfiedB k bs xs)
        => NB k as xs -> NB k bs xs
    goB (Cr x) = Cr (goP x)

    goP :: (AllE KFunctorField xs, ISatisfiedE k bs xs)
        => NP (NA k as) xs -> NP (NA k bs) xs
    goP Nil         = Nil
    goP (E x :* xs) = kmapf f (E x) :* goP xs
    goP (I   :* xs) = I :* goP xs

class KFunctorField (t :: Atom dtk Type) where
  kmapf :: Mappings as bs -> NA dtk as (Explicit t) -> NA dtk bs (Explicit t)

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
  kmapf f (E x) = E (go (styvar @k @v) f x)
    where go :: forall k (as :: LoT k) (bs :: LoT k) (v :: TyVar k Type)
              . STyVar k v -> Mappings as bs -> Ty k as (Var v) -> Ty k bs (Var v)
          go SVZ      (MCons g _)  x = g x
          go (SVS v') (MCons _ f') x = go v' f' x

instance KFunctorField (Kon t) where
  kmapf f (E x) = E x

instance forall f x. (KFunctorHead f, KFunctorField x) => KFunctorField (f :@: x) where
  kmapf f (E x) = E $ unA0 $ unArg
                $ kmaph (Proxy :: Proxy f) f (MCons (unE . kmapf f . E @_ @x) MNil)
                $ Arg $ A0 x

class KFunctorHead (t :: Atom dtk k) where
  kmaph :: SSLoT k ts => Proxy t
        -> Mappings as bs -> Mappings rs ts 
        -> ApplyT k (Ty dtk as t) rs -> ApplyT k (Ty dtk bs t) ts

instance forall f x. (KFunctorHead f, KFunctorField x) => KFunctorHead (f :@: x) where
  kmaph _ f r x = unArg
                $ kmaph (Proxy :: Proxy f) f (MCons (unE . kmapf f . E @_ @x) r)
                $ Arg x

instance forall k (f ::k). (KFunctor k f) => KFunctorHead (Kon f) where
  kmaph _ _ r x = kmap r x