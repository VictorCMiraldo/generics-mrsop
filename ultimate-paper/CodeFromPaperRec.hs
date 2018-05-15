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

data Atom (rtk :: Kind) (dtk :: Kind) k where
  Var    :: SNat n  -> Atom rtk dtk (Pos n dtk)
  Kon    :: k       -> Atom rtk dtk k
  (:@:)  :: Atom rtk dtk (k1 -> k2) -> Atom rtk dtk k1 -> Atom rtk dtk k2
  Rec    :: Atom rtk dtk rtk

type V0  = Var SZ
type V1  = Var (SS SZ)
type V2  = Var (SS (SS SZ))

type family Pos (n :: Nat) (dtk :: Kind) :: Kind where
  -- Pos n      Type       = TypeError (Text "Not found")
  Pos Z      (x -> xs)  = x
  Pos (S n)  (x -> xs)  = Pos n xs

infixr 5 :&&:
data LoT (dtk :: Kind) where
  LoT0    ::                LoT (*)
  (:&&:)  :: k -> LoT ks -> LoT (k -> ks)

type family Ty (rtk :: Kind) (dtk :: Kind) (r :: rtk) (tys :: LoT dtk) (t :: Atom rtk dtk k) :: k where
  Ty rtk (k1       -> ks) r (t1         :&&: ts) V0  = t1
  Ty rtk (k1 -> k2 -> ks) r (t1 :&&: t2 :&&: ts) V1  = t2
  Ty rtk dtk r tys (Kon t)   = t
  Ty rtk dtk r tys (f :@: x) = (Ty rtk dtk r tys f) (Ty rtk dtk r tys x)
  Ty rtk dtk r tys Rec       = r

data Field (rtk :: Kind) (dtk :: Kind) where
  Explicit  :: Atom rtk dtk (*)         -> Field rtk dtk
  Implicit  :: Atom rtk dtk Constraint  -> Field rtk dtk

data SKind (ell :: Kind) = KK

data Branch (rtk :: Kind) (dtk :: Kind) where
  Exists  :: SKind ell -> Branch rtk (ell -> dtk)   -> Branch rtk dtk
  Constr  :: [Field rtk dtk]                        -> Branch rtk dtk

type DataType dtk = [Branch dtk dtk]

data NA (rtk :: Kind) (dtk :: Kind) :: rtk -> LoT dtk -> Field rtk dtk -> * where
  E ::  forall rtk dtk t r tys .  { unE :: Ty rtk dtk r tys t } ->  NA rtk dtk r tys (Explicit t)
  I ::  forall rtk dtk t r tys .  Ty rtk dtk r tys t  =>  NA rtk dtk r tys (Implicit t)

infixr 5 :*
data NP :: (k -> *) -> [k] -> * where
  Nil  ::                    NP f '[]
  (:*) :: f x -> NP f xs ->  NP f (x ': xs)

data NB (rtk :: Kind) (dtk :: Kind) :: rtk -> LoT dtk -> Branch rtk dtk -> * where
  Ex  ::  forall ell (t :: ell) (p :: SKind ell) rtk dtk r tys c .
          NB rtk (ell -> dtk) r (t :&&: tys) c  -> NB rtk dtk r tys (Exists p c)
  Cr  ::  NP (NA rtk dtk r tys) fs              -> NB rtk dtk r tys (Constr fs)

data NS :: (k -> *) -> [k] -> * where
  Here   :: f k      -> NS f (k ': ks)
  There  :: NS f ks  -> NS f (k ': ks)

type SOPn dtk (c :: DataType dtk) (r :: dtk) (tys :: LoT dtk) = NS (NB dtk dtk r tys) c

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
  from  ::  ApplyT dtk f tys -> SOPn dtk (Code f) f tys
  to    ::  SSLoT dtk tys
        =>  SOPn dtk (Code f) f tys -> ApplyT dtk f tys

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

---

class FunctorField r (t :: Atom (* -> *) (* -> *) Type) where
  gfmapF  ::  (forall x y. (x -> y) -> r x -> r y)
          ->  (a -> b)
          ->  NA (* -> *) (* -> *) r (a :&&: LoT0) (Explicit t)
          ->  NA (* -> *) (* -> *) r (b :&&: LoT0) (Explicit t)
instance FunctorField r V0 where
  gfmapF r f (E x) = E (f x)
instance (Functor f, FunctorField r x) => FunctorField r (Kon f :@: x) where
  gfmapF r f (E x) = E (fmap (unE . gfmapF r f . E @_ @_ @x) x)
instance FunctorField r (Kon t) where
  gfmapF r f (E x) = E x
instance (FunctorField r x)
         => FunctorField r (Rec :@: x) where
  gfmapF r f (E x)
    = E (r (unE . gfmapF r f . E @_ @_ @x @r) x)

type family AllE2 c xs :: Constraint where
  AllE2 c '[] = ()
  AllE2 c (x ': xs) = (AllB c x, AllE2 c xs)

type family AllB c xs :: Constraint where
  AllB c (Constr x) = AllE c x

type family AllE c xs :: Constraint where
  AllE c '[] = ()
  AllE c (Explicit x ': xs) = (c x, AllE c xs)
  -- AllE c (Implicit x ': xs)

gfmap :: forall f a b
       . (GenericNSOP (* -> *) f,
          AllE2 (FunctorField f) (Code f))
      => (a -> b) -> f a -> f b
gfmap f = unravel . to
        . goS
        . from . ravel
  where
    goS :: AllE2 (FunctorField f) xs
        => NS (NB (* -> *) (* -> *) f (a :&&: LoT0)) xs
        -> NS (NB (* -> *) (* -> *) f (b :&&: LoT0)) xs
    goS (Here x)  = Here  (goB x)
    goS (There x) = There (goS x)

    goB :: AllB (FunctorField f) xs
        => NB (* -> *) (* -> *) f (a :&&: LoT0) xs
        -> NB (* -> *) (* -> *) f (b :&&: LoT0) xs
    goB (Cr x) = Cr (goP x)

    goP :: AllE (FunctorField f) xs
        => NP (NA (* -> *) (* -> *) f (a :&&: LoT0)) xs
        -> NP (NA (* -> *) (* -> *) f (b :&&: LoT0)) xs
    goP Nil         = Nil
    goP (E x :* xs) = gfmapF gfmap f (E x) :* goP xs

instance GenericNSOP (* -> *) [] where
  type Code [] = '[ Constr '[ ], Constr '[ Explicit V0, Explicit (Rec :@: V0) ] ]

  from (Arg (A0 [])) = Here $ Cr $ Nil
  from (Arg (A0 (x : xs))) = There $ Here $ Cr $ E @_ @_ @V0 x :* E xs :* Nil
  
  to :: forall tys. SSLoT (* -> *) tys
     => SOPn (* -> *) (Code []) [] tys -> ApplyT (* -> *) [] tys
  to sop = case sslot @(* -> *) @tys of
    SLoTA SLoT0 -> case sop of
      Here (Cr Nil) -> Arg $ A0 []
      There (Here (Cr (E x :* E xs :* Nil)))  -> Arg $ A0 $ x : xs

fmapList :: (a -> b) -> [a] -> [b]
fmapList = gfmap
-- fmapMaybe :: (a -> b) -> Maybe a -> Maybe b
-- fmapMaybe = gfmap
