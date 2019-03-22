{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternSynonyms     #-}
-- |Useful utilities we need accross multiple modules.
module Generics.MRSOP.Util
  ( -- * Utility Functions and Types
    (&&&) , (***)
  , (:->) , (<.>)

    -- * Poly-kind indexed product functionality
  , Product(..), (:*:), pattern (:*:) , Delta , curry' , uncurry' , delta

    -- * Poly-kind indexed sums
  , Sum(..) , either' , either''

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
  , EqHO(..) , ShowHO(..)
  ) where

import Data.Proxy
import Data.Type.Equality
import Data.Functor.Product
import Data.Functor.Sum
import Data.Functor.Const
import GHC.TypeLits (TypeError , ErrorMessage(..))
import Control.Arrow ((***) , (&&&))

type    (:*:)     = Product

pattern (:*:) :: f a -> g a -> Product f g a
pattern (:*:) x y = Pair x y

-- |Lifted curry
curry' :: (Product f g x -> a) -> f x -> g x -> a
curry' f fx gx = f (Pair fx gx)

-- |Lifted uncurry
uncurry' :: (f x -> g x -> a) -> Product f g x -> a
uncurry' f (Pair fx gx) = f fx gx

-- |Natural transformations
type f :-> g = forall n . f n -> g n

-- |Diagonal indexed functor
type Delta f = Product f f

-- |Duplicates its argument
delta :: f :-> Delta f
delta fx = Pair fx fx

-- |Higher-order sum eliminator
either' :: (f :-> r) -> (g :-> r) -> Sum f g :-> r
either' f _ (InL x) = f x
either' _ g (InR x) = g x

-- |Just like 'either'', but the result type is of kind Star
either'' :: (f :-> Const a) -> (g :-> Const a) -> Sum f g x -> a
either'' f g = getConst . either' f g

infixr 8 <.>
-- |Kleisli Composition
(<.>) :: (Monad m) => (b -> m c) -> (a -> m b) -> a -> m c
f <.> g = (>>= f) . g

-- |Type-level Peano Naturals
data Nat = S Nat | Z
  deriving (Eq , Show)

proxyUnsuc :: Proxy ('S n) -> Proxy n
proxyUnsuc _ = Proxy

-- |Singleton Term-level natural
data SNat :: Nat -> * where
  SZ ::           SNat 'Z
  SS :: SNat n -> SNat ('S n)

snat2int :: SNat n -> Integer
snat2int SZ     = 0
snat2int (SS n) = 1 + snat2int n

-- |And their conversion to term-level integers.
class IsNat (n :: Nat) where
  getSNat :: Proxy n -> SNat n
instance IsNat 'Z where
  getSNat _ = SZ
instance IsNat n => IsNat ('S n) where
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
  Lkup 'Z     (k : ks) = k
  Lkup ('S n) (k : ks) = Lkup n ks
  Lkup _      '[]      = TypeError ('Text "Lkup index too big")

-- |Type-level list index
type family Idx (ty :: k) (xs :: [k]) :: Nat where
  Idx x (x ': ys) = 'Z
  Idx x (y ': ys) = 'S (Idx x ys)
  Idx x '[]       = TypeError ('Text "Element not found")

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
class EqHO (f :: ki -> *) where
  eqHO :: forall k . f k -> f k -> Bool

instance Eq a => EqHO (Const a) where
  eqHO (Const a) (Const b) = a == b

instance (EqHO f, EqHO g) => EqHO (Product f g) where
  eqHO (Pair fx gx) (Pair fy gy) = eqHO fx fy && eqHO gx gy

instance (EqHO f, EqHO g) => EqHO (Sum f g) where
  eqHO (InL fx) (InL fy) = eqHO fx fy
  eqHO (InR gx) (InR gy) = eqHO gx gy
  eqHO _        _        = False

-- |Higher order version of 'Show'
class ShowHO (f :: ki -> *) where
  showHO :: forall k . f k -> String

instance Show a => ShowHO (Const a) where
  showHO (Const a) = show a

instance (ShowHO f , ShowHO g) => ShowHO (Product f g) where
  showHO (Pair x y) = "(" ++ showHO x ++ ", " ++ showHO y ++ ")"

instance (ShowHO f , ShowHO g) => ShowHO (Sum f g) where
  showHO (InL fx) = "InL " ++ showHO fx
  showHO (InR gx) = "InR " ++ showHO gx

