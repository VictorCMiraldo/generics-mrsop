{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeOperators    #-}
{-# LANGUAGE PolyKinds        #-}
{-# LANGUAGE Arrows           #-}
module Generics.MRSOP.AG.Higher where

import Prelude
import Data.Functor.Const
import Data.Functor.Product
import Data.Monoid (Sum(..), (<>))

import Generics.MRSOP.Base
import Generics.MRSOP.Util
import Generics.MRSOP.AG hiding (AG(..))

type f :~>: g = forall x. f x -> g x

newtype AG ki codes chi phi
  = AG { unAG :: AnnFix ki codes chi :~>: AnnFix ki codes phi }

overConst :: (a -> b) -> Const a t -> Const b t
overConst f (Const x) = Const (f x)

type f :&: g = Product f g

-- From 'Arrow'
-- arr :: (a -> b) -> AG ki codes (Const a) (Const b)
-- arr f = AG $ mapAnn (overConst f)

arr :: (a :~>: b) -> AG ki codes a b
arr f = AG $ mapAnn f

(>>>) :: AG ki codes a b -> AG ki codes b c -> AG ki codes a c
AG ab >>> AG bc = AG (bc . ab)

returnA :: AG ki codes x x
returnA = arr id

fst1 :: (f :&: g) :~>: f
fst1 (Pair x _) = x

snd1 :: (f :&: g) :~>: g
snd1 (Pair _ y) = y

first :: AG ki codes f g -> AG ki codes (f :&: h) (g :&: h)
first (AG ag) = AG $ \x -> zipAnn Pair (ag (mapAnn fst1 x)) (mapAnn snd1 x)

loop :: AG ki codes (f :&: h) (g :&: h) -> AG ki codes f g
loop (AG ag) = AG $ \b -> let bd = zipAnn Pair b d
                              cd = ag bd
                              c = mapAnn fst1 cd
                              d = mapAnn snd1 cd
                          in c

data Unit (a :: k) = Unit

unitAnn :: Fix ki codes :~>: AnnFix ki codes Unit
unitAnn = synthesize (\_ -> Unit)

runAG :: AG ki codes Unit r -> Fix ki codes :~>: AnnFix ki codes r
runAG (AG ag) = ag . unitAnn

sizeGenericAG :: AG ki codes a (Const (Sum Int))
sizeGenericAG = AG $ synthesizeAnn (\_ -> sizeAlgebra)

depthGenericAG :: AG ki codes a (Const Int)
depthGenericAG = AG $ inheritAnn (\_ r (Const n) -> mapRep (const (Const (n+1))) r) 0

-- CANNOT USE ARROW SYNTAX ON NON-* KINDS!!
{-
sizeTwiceDepth :: AG ki codes a (Product (Const (Sum Int)) (Const Int))
sizeTwiceDepth = proc x -> do Const r <- sizeGenericAG -< x
                              d <- depthGenericAG -< x
                              returnA -< Pair (Const (r + r)) d
-}