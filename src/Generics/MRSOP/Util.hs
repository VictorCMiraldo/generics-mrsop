{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# OPTIONS_GHC -Wno-orphans       #-}
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
  , EqHO , ShowHO
  ) where

import Data.Proxy
import Data.Type.Equality
import Data.Functor.Product
import Data.Functor.Sum
import Data.Functor.Const
import GHC.TypeLits (TypeError , ErrorMessage(..))
import Control.Arrow ((***) , (&&&))

-- |Convenient type synonym for 'Product'
type    (:*:)     = Product

-- |Convnient pattern synonym for 'Pair'
pattern (:*:) :: f a -> g a -> Product f g a
pattern (:*:) x y = Pair x y
{-# COMPLETE (:*:) #-}

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
either'' :: (forall x . f x -> a) -> (forall y . g y -> a) -> Sum f g r -> a
either'' f g = getConst . either' (Const . f) (Const . g)

infixr 8 <.>
-- |Kleisli Composition
(<.>) :: (Monad m) => (b -> m c) -> (a -> m b) -> a -> m c
f <.> g = (>>= f) . g

-- |Type-level Peano Naturals
data Nat = S Nat | Z
  deriving (Eq , Show)

-- |Typelevel predecessor operation
proxyUnsuc :: Proxy ('S n) -> Proxy n
proxyUnsuc _ = Proxy

-- |Singleton Term-level natural
data SNat :: Nat -> * where
  SZ ::           SNat 'Z
  SS :: SNat n -> SNat ('S n)

-- |Returns @n@ as a first class integer.
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
  LP_Nil  :: ListPrf '[]
  LP_Cons :: ListPrf l ->  ListPrf (x ': l)

-- |The @IsList@ class allows us to construct
--  'ListPrf's in a straight forward fashion.
class IsList (xs :: [k]) where
  listPrf :: ListPrf xs
instance IsList '[] where
  listPrf = LP_Nil
instance IsList xs => IsList (x ': xs) where
  listPrf = LP_Cons listPrf

-- |Concatenation of lists is also a list.
appendIsListLemma :: ListPrf xs -> ListPrf ys -> ListPrf (xs :++: ys)
appendIsListLemma LP_Nil         isys = isys
appendIsListLemma (LP_Cons isxs) isys = LP_Cons (appendIsListLemma isxs isys)

-- |Appending type-level lists
type family (:++:) (txs :: [k]) (tys :: [k]) :: [k] where
  (:++:) '[] tys = tys
  (:++:) (tx ': txs) tys = tx ': (txs :++: tys)

-- |Convenient constraint synonyms
type L1 xs          = (IsList xs) 
type L2 xs ys       = (IsList xs, IsList ys) 
type L3 xs ys zs    = (IsList xs, IsList ys, IsList zs) 
type L4 xs ys zs as = (IsList xs, IsList ys, IsList zs, IsList as) 

-- |Constraint synonym replacing the old @EqHO@ hack.
-- @since 2.2.0
type EqHO   f = forall x . Eq   (f x)

-- |Constraint synonym replacing the old @ShowHO@ hack.
-- @since 2.2.0
type ShowHO f = forall x . Show (f x)

instance (EqHO f , EqHO g) => Eq ((f :*: g) x) where
  (fx :*: gx) == (fy :*: gy) = fx == fy && gx == gy

instance (EqHO f , EqHO g) => Eq (Sum f g x) where
  (InL x) == (InL y) = x == y
  (InR x) == (InR y) = x == y
  _       == _       = False

