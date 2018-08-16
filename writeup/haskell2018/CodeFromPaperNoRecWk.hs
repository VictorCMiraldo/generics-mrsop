{-# language DataKinds                 #-}
{-# language ConstraintKinds           #-}
{-# language ExplicitNamespaces        #-}
{-# language TypeOperators             #-}
{-# language GADTs                     #-}
{-# language TypeFamilies              #-}
{-# language PolyKinds                 #-}
{-# language ExistentialQuantification #-}
{-# language InstanceSigs              #-}
{-# language TypeApplications          #-}
{-# language FlexibleInstances         #-}
{-# language MultiParamTypeClasses     #-}
{-# language FunctionalDependencies    #-}
{-# language PatternSynonyms           #-}
{-# language TypeInType                #-}
{-# language ScopedTypeVariables       #-}
{-# language FlexibleContexts          #-}
{-# language FlexibleInstances         #-}
{-# language RankNTypes                #-}
module CodeFromPaperNoRecWk where

import Data.Kind (type (*), type Type, Constraint)
import Data.Proxy

type Kind = (*)

data Nat = Z | S Nat

data SNat (n :: Nat) where
  SZ :: SNat Z
  SS :: SNat n -> SNat (S n)

type family Args (k :: Kind) :: [Kind] where
  Args (k -> dtk) = k ': Args dtk
  Args k          = '[]

data Atom (dtk :: [Kind]) (k :: Kind) :: Kind where
  Var    ::               Atom (k  ': dtk) k
  Wk     :: Atom dtk k -> Atom (k0 ': dtk) k
  Kon    :: k          -> Atom dtk k
  (:@:)  :: Atom dtk (k1 -> k2)
         -> Atom dtk k1
         -> Atom dtk k2

data Id a = Id a

type family Ty (dtk :: [Kind]) (tys :: NP Id dtk) (t :: Atom dtk k) :: k where
  Ty (k : dtk) ('Id a :* vs) Var = a
  Ty (k : dtk) (_    :* vs) (Wk t) = Ty dtk vs t
  Ty dtk tys (Kon t)   = t
  Ty dtk tys (f :@: x) = (Ty dtk tys f) (Ty dtk tys x)

data Field (dtk :: [Kind]) where
  Explicit  :: Atom dtk (*)         -> Field dtk
  Implicit  :: Atom dtk Constraint  -> Field dtk

data SKind (ell :: Kind) = KK

data Branch (dtk :: [Kind]) where
  Exists  :: SKind ell -> Branch (ell ': dtk)   -> Branch dtk
  Constr  :: [Field dtk]                        -> Branch dtk

type DataType dtk = [Branch dtk]

data NA (dtk :: [Kind]) :: NP Id dtk -> Field dtk -> * where
  E ::  forall dtk t tys .  Ty dtk tys t  ->  NA dtk tys (Explicit t)
  I ::  forall dtk t tys .  Ty dtk tys t  =>  NA dtk tys (Implicit t)

data NP :: (k -> *) -> [k] -> * where
  Nil  ::                    NP f '[]
  (:*) :: f x -> NP f xs ->  NP f (x ': xs)

data NS :: (k -> *) -> [k] -> * where
  Here   :: f k      -> NS f (k ': ks)
  There  :: NS f ks  -> NS f (k ': ks)

data NB (dtk :: [Kind]) :: NP Id dtk -> Branch dtk -> * where
  Ex  ::  forall ell (t :: ell) (p :: SKind ell) dtk tys c .
          NB (ell ': dtk) ('Id t :* tys) c -> NB dtk tys (Exists p c)
  Cr  ::  NP (NA dtk tys) fs               -> NB dtk tys (Constr fs)

type SOPn dtk (c :: DataType dtk) (tys :: NP Id dtk) = NS (NB dtk tys) c

{-
data SNP dtk (tys :: NP Id dtk) where
  SNP Id0  ::                   SNP (*)     NP Id0
  SNP IdA  ::  SNP Id ks ts ->  SNP (k -> ks)  (t :&&: ts)

class SSNP Id k (tys :: NP Id k) where
  sslot :: SNP Id k tys
instance SSNP Id (*) NP Id0 where
  sslot = SNP Id0
instance SSNP Id ks ts => SSNP Id (k -> ks) (t :&&: ts) where
  sslot = SNP IdA sslot
-}

data ApplyT (dtk :: Kind) (f :: dtk) (tys :: NP Id (Args dtk)) :: * where
  A0   :: { unA0   ::  f  }
       -> ApplyT (*)     f  Nil
  Arg  :: forall k ks (t :: k) ts f
        . { unArg  ::  ApplyT ks (f t) ts  }
       -> ApplyT (k -> ks)  f ('Id t :* ts)
{-
class GenericNSOP (dtk :: Kind) (f :: dtk) where
  type Code f :: DataType (Args dtk)
  from  ::  ApplyT (Args dtk) f tys -> SOPn (Args dtk) (Code f) tys
  to    ::  SOPn (Args dtk) (Code f) tys -> ApplyT (Args dtk) f tys

type family Apply (dtk :: [Kind]) (f :: ToKind dtk) (tys :: NP Id dtk) :: (*) where
  Apply '[]       f Nil            = f
  Apply (k ': ks) f ('Id t :* ts)  = Apply ks (f t) ts

unravel :: ApplyT k f ts -> Apply k f ts
unravel (A0   x) = x
unravel (Arg  x) = unravel x

data ListPrf (x :: [Kind]) (fx :: NP Id x) :: * where
  NilPrf :: ListPrf '[] Nil
  ConsPrf :: ListPrf xs fxs -> ListPrf (x ': xs) ('Id fx :* fxs)

{-
ravel :: forall dtk f (ts :: NP Id dtk)
       . ListPrf dtk ts -> Apply dtk f ts -> ApplyT dtk f ts
ravel NilPrf        f = A0 f
ravel (ConsPrf prf) f = Arg (ravel prf _) -- (ravel prf f)
  where
    reduce :: forall k dtk f ty tys
            . Proxy k -> Proxy dtk -> Proxy f
           -> Proxy ty -> Proxy tys
           -> Apply (k ': dtk) f ('Id ty :* tys)
           -> Apply dtk (f ty) tys
    reduce = _
-}
{-
ravel  ::  forall k f ts . Apply k f ts -> ApplyT k f ts
ravel = go (sslot @_ @ts)
  where
    go  ::  forall k f ts . SNP Id k ts
        ->  Apply k f ts -> ApplyT k f ts
    go SNP Id0       x = A0   x
    go (SNP IdA ts)  x = Arg  (go ts x)
-}
-}
