{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- |Useful utilities we need accross multiple modules.
module Generics.MRSOP.Util
  ( -- * Utility Functions and Types
    (&&&) , (***)
  , (:->) , (<.>)

    -- * Poly-kind indexed product
  , (:*:)(..) , curry' , uncurry'

    -- * Type-level Naturals
  , Nat(..) , proxyUnsuc
  , SNat(..) , snat2int
  , IsNat(..) , getNat , getSNat'

    -- * Type-level Lists
  , ListPrf(..) , IsList(..)
  , L1 , L2 , L3 , L4
  , (:++:) , appendIsListLemma

    -- * Type-level List Lookup
  , Lkup , Idx , El(..) , getElSNat , into

    -- * Higher-order Eq and Show
  , Eq1(..) , Show1(..)
  ) where

import Data.Proxy
import Data.Type.Equality
import GHC.TypeLits (TypeError , ErrorMessage(..))

infixr 3 *** , &&&
(&&&) :: (a -> b) -> (a -> c) -> a -> (b , c)
f &&& g = \x -> (f x , g x)

(***) :: (a -> b) -> (c -> d) -> (a , c) -> (b , d)
f *** g = (f . fst) &&& (g . snd)

-- |Poly-kind-indexed product
data (:*:) (f :: k -> *) (g :: k -> *) (x :: k)
  = f x :*: g x

-- |Lifted curry
curry' :: ((f :*: g) x -> a) -> f x -> g x -> a
curry' f fx gx = f (fx :*: gx)

-- |Lifted uncurry
uncurry' :: (f x -> g x -> a) -> (f :*: g) x -> a
uncurry' f (fx :*: gx) = f fx gx

-- |Natural transformations
type f :-> g = forall n . f n -> g n

infixr 8 <.>
-- |Kleisli Composition
(<.>) :: (Monad m) => (b -> m c) -> (a -> m b) -> a -> m c
f <.> g = (>>= f) . g

-- |Type-level Peano Naturals
data Nat = S Nat | Z
  deriving (Eq , Show)

proxyUnsuc :: Proxy (S n) -> Proxy n
proxyUnsuc _ = Proxy

-- |Singleton Term-level natural
data SNat :: Nat -> * where
  SZ ::           SNat Z
  SS :: SNat n -> SNat (S n)

snat2int :: SNat n -> Integer
snat2int SZ     = 0
snat2int (SS n) = 1 + snat2int n

-- |And their conversion to term-level integers.
class IsNat (n :: Nat) where
  getSNat :: Proxy n -> SNat n
instance IsNat Z where
  getSNat p = SZ
instance IsNat n => IsNat (S n) where
  getSNat p = SS (getSNat $ proxyUnsuc p)

getNat :: (IsNat n) => Proxy n -> Integer
getNat = snat2int . getSNat

getSNat' :: forall (n :: Nat). IsNat n => SNat n
getSNat' = getSNat (Proxy :: Proxy n)

instance TestEquality SNat where
  testEquality SZ     SZ     = Just Refl
  testEquality (SS n) (SS m)
    = case testEquality n m of
        Nothing   -> Nothing
        Just Refl -> Just Refl
  testEquality _      _      = Nothing

-- |Type-level list lookup
type family Lkup (n :: Nat) (ks :: [k]) :: k where
  Lkup Z     (k : ks) = k
  Lkup (S n) (k : ks) = Lkup n ks
  Lkup _     '[]      = TypeError (Text "Lkup index too big")

-- |Type-level list index
type family Idx (ty :: k) (xs :: [k]) :: Nat where
  Idx x (x ': ys) = Z
  Idx x (y ': ys) = S (Idx x ys)
  Idx x '[]       = TypeError (Text "Element not found")

-- |Also list lookup, but for kind * only.
data El :: [*] -> Nat -> * where
  El :: IsNat ix => {unEl :: Lkup ix fam} -> El fam ix

-- | Convenient way to cast an 'El' index to term-level.
getElSNat :: forall ix ls. El ls ix -> SNat ix
getElSNat (El _) = getSNat' @ix

-- |Smart constructor into 'El'
into :: forall fam ty ix
      . (ix ~ Idx ty fam , Lkup ix fam ~ ty , IsNat ix)
     => ty -> El fam ix
into = El


-- |An inhabitant of @ListPrf ls@ is *not* a singleton!
--  It only proves that @ls@ is, in fact, a type level list.
--  This is useful since it enables us to pattern match on
--  type-level lists whenever we see fit.
data ListPrf :: [k] -> * where
  Nil ::  ListPrf '[]
  Cons :: ListPrf l ->  ListPrf (x ': l)

-- |The @IsList@ class allows us to construct
--  'ListPrf's in a straight forward fashion.
class IsList (xs :: [k]) where
  listPrf :: ListPrf xs
instance IsList '[] where
  listPrf = Nil
instance IsList xs => IsList (x ': xs) where
  listPrf = Cons listPrf

-- |Concatenation of lists is also a list.
appendIsListLemma :: ListPrf xs -> ListPrf ys -> ListPrf (xs :++: ys)
appendIsListLemma Nil         isys = isys
appendIsListLemma (Cons isxs) isys = Cons (appendIsListLemma isxs isys)

-- |Appending type-level lists
type family (:++:) (txs :: [k]) (tys :: [k]) :: [k] where
  (:++:) '[] tys = tys
  (:++:) (tx ': txs) tys = tx ': (txs :++: tys)

-- |Convenient constraint synonyms
type L1 xs          = (IsList xs) 
type L2 xs ys       = (IsList xs, IsList ys) 
type L3 xs ys zs    = (IsList xs, IsList ys, IsList zs) 
type L4 xs ys zs as = (IsList xs, IsList ys, IsList zs, IsList as) 

-- TODO: VCM: looking at the implementation for the instances
--            in Generics.MRSOP.Opaque, it seems like we don't really need this.

-- |Higher order version of 'Eq'
class Eq1 (f :: k -> *) where
  eq1 :: forall k . f k -> f k -> Bool

-- |Higher order version of 'Show'
class Show1 (f :: k -> *) where
  show1 :: forall k . f k -> String

