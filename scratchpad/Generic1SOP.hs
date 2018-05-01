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
module Generic1SOP where

import Data.Kind (type (*), type Type)

data Atom = Var | Rec (* -> *) | Kon (*)

data NS :: (k -> *) -> [k] -> * where
  Here   :: f k      -> NS f (k ': ks)
  There  :: NS f ks  -> NS f (k ': ks)

infixr 5 :*
data NP :: (k -> *) -> [k] -> * where
  Nil  ::                    NP f '[]
  (:*) :: f x -> NP f xs ->  NP f (x ': xs)

data NA :: * -> Atom -> * where
  V :: a   -> NA a Var
  R :: f a -> NA a (Rec f)
  K :: k   -> NA a (Kon k)

type SOP1 c a = NS (NP (NA a)) c

class Generic1SOP (f :: * -> *) where
  type Code1 f :: [[Atom]]
  from :: f a -> SOP1 (Code1 f) a
  to   :: SOP1 (Code1 f) a -> f a

data Tree a = Leaf | Node (Tree a) a (Tree a)

instance Generic1SOP Tree where
  type Code1 Tree = '[ '[], '[ Rec Tree, Var, Rec Tree ] ]

  from Leaf         = Here Nil
  from (Node l x r) = There $ Here $ R l :* V x :* R r :* Nil

  to (Here Nil) = Leaf
  to (There (Here (R l :* V x :* R r :* Nil))) = Node l x r