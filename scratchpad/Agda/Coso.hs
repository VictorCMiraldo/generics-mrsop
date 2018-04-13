{-# language DataKinds #-}
{-# language TypeInType #-}
{-# language ConstraintKinds #-}
{-# language ExplicitNamespaces #-}
{-# language TypeOperators #-}
{-# language GADTs #-}
{-# language TypeFamilies #-}
{-# language PolyKinds #-}
{-# language InstanceSigs #-}
{-# language ScopedTypeVariables #-}
{-# language TypeApplications #-}
module Coso where

import Data.Kind (type (*))
import GHC.Exts (Constraint)

type DT    = [Con]
type Con   = ( [* -> Constraint],
               [Field (*) (Maybe (* -> *)) (Maybe (* -> *)) (Maybe (* -> *))] )
data Field k v post pre
           = Kon k
           | Var v
           | Rec post pre

type SCon ps = '( '[], ps )
type SVar = Var Nothing
type SRec = Rec Nothing Nothing

data NS f xs a where
  Here  :: f x a     -> NS f (x ': xs) a
  There :: NS f xs a -> NS f (x ': xs) a

data NC f branch a where
  B :: All cs a => NP f xs a -> NC f '(cs, xs) a

type family All cs a :: Constraint where
  All '[]       a = ()
  All (c ': cs) a = (c a, All cs a)

infixr 5 :*:
data NP f xs a where
  NP0   :: NP f '[] a
  (:*:) :: f x a -> NP f xs a -> NP f (x ': xs) a

type family May fs a where
  May 'Nothing  a = a
  May ('Just f) a = f a

data NF r field a where
  K :: t                        -> NF r (Kon t) a
  V :: May g a                  -> NF r (Var g) a
  R :: May post (r (May pre a)) -> NF r (Rec post pre) a

type N r dt a = NS (NC (NF r)) dt a

newtype Fix dt a = Fix { unFix :: N (Fix dt) dt a }

type List = '[ SCon '[], SCon '[SVar, SRec] ]

class Generic1 f where
  type Rep f :: DT
  to   :: f a -> Fix (Rep f) a
  from :: Fix (Rep f) a -> f a

instance Generic1 [] where
  type Rep [] = List

  to []     = Fix $ Here (B NP0)
  to (x:xs) = Fix $ There $ Here $ B $
                V x :*: R (to xs) :*: NP0
  
  from :: forall a. Fix List a -> [a]
  from (Fix (Here (B NP0))) = []
  from (Fix (There (Here (B (V x :*: R xs :*: NP0))))) = x : from xs

data X a where
  XInt :: Int -> X Int
       -- Int ~ a => Int -> X a

instance Generic1 X where
  type Rep X = '[ '( '[ (~) Int ], '[ Kon Int ]) ]

  to (XInt n) = Fix $ Here $ B $ K n :*: NP0
  from (Fix (Here (B (K n :*: NP0)))) = XInt n