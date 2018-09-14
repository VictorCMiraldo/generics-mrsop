{-# language PolyKinds, DataKinds, KindSignatures, TypeInType #-}
{-# language GADTs, TypeOperators, TypeFamilies, ConstraintKinds #-}
{-# language ExistentialQuantification #-}
{-# language MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{-# language PatternSynonyms, ScopedTypeVariables, InstanceSigs #-}
{-# language FunctionalDependencies, TypeApplications, FlexibleContexts #-}
module PatternFunctors where

import Data.Kind

data U x         = U
data (f :+: g) x = InL (f x) | InR (g x)
data (f :*: g) x = f x :*: g x

data TyVar (d :: *) k where
  VZ :: TyVar (x -> xs) x
  VS :: TyVar xs k -> TyVar (x -> xs) k

data Atom (d :: *) k where
  Var   :: TyVar d k -> Atom d k
  Kon   :: k         -> Atom d k
  (:@:) :: Atom d (k1 -> k2) -> Atom d k1 -> Atom d k2

type f :$: x = Kon f :@: x
type a :~: b = Kon (~) :@: a :@: b

type V0  = Var VZ
type V1  = Var (VS VZ)
type V2  = Var (VS (VS VZ))

infixr 5 :&&:
data LoT (d :: *) where
  LoT0    ::                LoT (*)
  (:&&:)  :: k -> LoT ks -> LoT (k -> ks)

type family Ty (d :: *) (tys :: LoT d) (t :: Atom d k) :: k where
  Ty (k -> ks) (t :&&: ts) (Var VZ)     = t
  Ty (k -> ks) (t :&&: ts) (Var (VS v)) = Ty ks ts (Var v)
  Ty d tys (Kon t)   = t
  Ty d tys (f :@: x) = (Ty d tys f) (Ty d tys x)

newtype F (t :: Atom d (*)) (x :: LoT d) = F { unF :: Ty d x t }
data C (t :: Atom d Constraint) (x :: LoT d) where
  C :: Ty d x t => C t x

data E (k :: *) (f :: LoT (k -> d) -> *) (x :: LoT d) where
  E :: forall (k :: *) (t :: k) (d :: *) (f :: LoT (k -> d) -> *) (x :: LoT d)
     . f (t :&&: x) -> E k f x

data ApplyT k (f :: k) (tys :: LoT k) :: * where
  A0  :: { unA0  :: f } -> ApplyT (*) f  LoT0
  Arg :: { unArg :: ApplyT ks (f t) ts } -> ApplyT (k -> ks) f (t :&&: ts)

type (f :: k) :@@: (x :: LoT k) = ApplyT k f x

data SLoT dtk (tys :: LoT dtk) where
  SLoT0  ::               SLoT (*)       LoT0
  SLoTA  :: SLoT ks ts -> SLoT (k -> ks) (t :&&: ts)

pattern SLoT1 = SLoTA SLoT0
pattern SLoT2 = SLoTA SLoT1
pattern SLoT3 = SLoTA SLoT2

class SSLoT (tys :: LoT k) where
  sslot :: SLoT k tys
instance SSLoT LoT0 where
  sslot = SLoT0
instance SSLoT ts => SSLoT (t :&&: ts) where
  sslot = SLoTA sslot

unravel :: f :@@: ts -> Apply k f ts
unravel (A0   x) = x
unravel (Arg  x) = unravel x

ravel  ::  forall k f ts . SSLoT ts 
       =>  Apply k f ts -> f :@@: ts
ravel = go (sslot @_ @ts)
  where
    go  ::  forall k f ts . SLoT k ts
        ->  Apply k f ts -> ApplyT k f ts
    go SLoT0       x = A0   x
    go (SLoTA ts) x = Arg (go ts x)

type family Apply k (f :: k) (tys :: LoT k) :: * where
  Apply (*)       f LoT0        = f
  Apply (k -> ks) f (a :&&: as) = Apply ks (f a) as

class Generic (f :: k) where
  type Rep f :: LoT k -> *
  from :: f :@@: x -> Rep f x
  to   :: SLoT k x -> Rep f x -> f :@@: x

instance Generic [] where
  type Rep [] = U :+: (F V0 :*: F (Kon [] :@: V0))

  from (Arg (A0 []))     = InL U
  from (Arg (A0 (x:xs))) = InR (F x :*: F xs)

  to SLoT1 (InL U) = Arg $ A0 $ []
  to SLoT1 (InR (F x :*: F xs)) = Arg $ A0 $ x : xs

data Equals a b where
  Refl :: Equals a a

instance Generic Equals where
  type Rep Equals = C (V0 :~: V1)

  from (Arg (Arg (A0 Refl))) = C
  to   SLoT2 C = Arg $ Arg $ A0 $ Refl

data X where
  X :: a -> X

instance Generic X where
  type Rep X = E (*) (F V0)

  from (A0 (X x)) = E (F x)
  to   SLoT0 (E (F x)) = A0 $ X x

type family AllShowG (l :: LoT k) :: Constraint where
  AllShowG LoT0 = ()
  AllShowG (x :&&: xs) = (ShowG x, AllShowG xs)

class ShowG (f :: k) where
  showg :: AllShowG x => f :@@: x -> String

instance ShowG Int where
  showg (A0 n) = show n

instance ShowG Maybe where
  showg (Arg (A0 Nothing))  = "Nothing"
  showg (Arg (A0 (Just x))) = "Just (" ++ showg (A0 x) ++ ")"


data Variance = Co | Contra | Inv

infixr 5 :.:
data Variances k where
  Vari0 :: Variances (*)
  (:.:) :: Variance -> Variances ks -> Variances (* -> ks)

data Mapping (v :: Variance) a b where
  CoM     :: (a -> b) -> Mapping Co a b
  ContraM :: (b -> a) -> Mapping Contra a b
  InvM    :: (a -> b, b -> a) -> Mapping Inv a b

infixr 5 :..:
data Mappings (v :: Variances k) (as :: LoT k) (bs :: LoT k) where
  M0 :: Mappings Vari0 LoT0 LoT0
  (:..:) :: Mapping v a b -> Mappings vs as bs
         -> Mappings (v :.: vs) (a :&&: as) (b :&&: bs)

class FunctorG (f :: k) (vs :: Variances k) | f -> vs where
  fmapG :: Mappings vs as bs -> f :@@: as -> f :@@: bs

instance FunctorG [] (Co :.: Vari0) where
  fmapG (CoM f :..: M0) (Arg (A0 xs)) = Arg $ A0 $ map f xs

instance FunctorG (->) (Contra :.: Co :.: Vari0) where
  fmapG (ContraM f :..: CoM g :..: M0) (Arg (Arg (A0 h)))
    = Arg $ Arg $ A0 $ g . h . f

type Profunctor f = FunctorG f (Contra :.: Co :.: Vari0)

dimap :: Profunctor f => (b -> a) -> (c -> d) -> f a c -> f b d
dimap f g = unravel . fmapG (ContraM f :..: CoM g :..: M0) . ravel