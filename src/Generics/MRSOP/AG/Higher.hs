{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeOperators    #-}
{-# LANGUAGE PolyKinds        #-}
{-# LANGUAGE Arrows           #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE PatternSynonyms  #-}
{-# LANGUAGE TypeApplications #-}
module Generics.MRSOP.AG.Higher where

import Prelude
import Data.Coerce
import Data.Functor.Const
import Data.Functor.Product
import Data.Monoid (Sum(..), (<>))

import Generics.MRSOP.Base
import Generics.MRSOP.Util
import Generics.MRSOP.Opaque
import Generics.MRSOP.AG hiding (AG(..))

import Generics.MRSOP.Examples.LambdaAlphaEqTH

type f :~>: g = forall x. f x -> g x

newtype AG ki codes chi phi
  = AG { unAG :: AnnFix ki codes chi :~>: AnnFix ki codes phi }

overConst :: (a -> b) -> Const a t -> Const b t
overConst f (Const x) = Const (f x)

type f :&: g = Product f g
type a :&&: b = Const a :&: Const b

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

unitAnn :: IsNat x => Fix ki codes x -> AnnFix ki codes Unit x
unitAnn = synthesize (\_ _ -> Unit)

runAG :: IsNat x => AG ki codes Unit r -> Fix ki codes x -> AnnFix ki codes r x
runAG (AG ag) = ag . unitAnn

runAG_ :: (Family ki fam codes, ix ~ Idx ty fam, Lkup ix fam ~ ty, IsNat ix)
       => AG ki codes Unit r -> ty -> AnnFix ki codes r ix
runAG_ ag = runAG ag . deep

sizeGenericAG :: AG ki codes a (Const (Sum Int))
sizeGenericAG = AG $ synthesize (\_ -> sizeAlgebra)

depthGenericAG :: AG ki codes a (Const Int)
depthGenericAG = AG $ inherit (\_ r (Const n) -> mapRep (const (Const (n+1))) r) 0

-- CANNOT USE ARROW SYNTAX ON NON-* KINDS!!
{-
sizeTwiceDepth :: AG ki codes a (Product (Const (Sum Int)) (Const Int))
sizeTwiceDepth = proc x -> do Const r <- sizeGenericAG -< x
                              d <- depthGenericAG -< x
                              returnA -< Pair (Const (r + r)) d
-}

duplicate :: x :~>: (x :&: x)
duplicate x = Pair x x

swap :: (x :&: y) :~>: (y :&: x)
swap (Pair x y) = Pair y x

sizeTwiceDepth :: AG ki codes a (Sum Int :&&: Int)
sizeTwiceDepth = arr duplicate
                 >>> first sizeGenericAG
                 >>> arr swap
                 >>> first depthGenericAG
                 >>> arr (\(Pair d (Const r)) -> Pair (Const $ r + r) d)

-- Example over lambda-terms

data Type = TyVar String | Arrow Type Type deriving (Show)
data TyEq = Type :=: Type deriving (Show)

type Context = [(String, Type)]

pattern Pair_ x y = Pair (Const x) (Const y)

copy :: (forall ix. f ix)
     -> Rep ki g c
     -> Rep ki f c
copy x = mapRep (const x)

type InhDefn ki codes a b
  = forall ix. a ix
               -> Rep ki (Const ()) (Lkup ix codes)
               -> b ix
               -> Rep ki b (Lkup ix codes)

type SynDefn ki codes a b
  = forall ix. a ix
               -> Rep ki b (Lkup ix codes)
               -> b ix

unique :: AG Singl CodesTerm a (Const String)
unique = AG $ inherit go (Const "x")
  where go :: InhDefn Singl CodesTerm a (Const String)
        go _ x (Const u) = case sop x of
          Abs_ v _ -> fromView $ Abs_ v (Const ('x':u))
          App_ f e -> fromView $ App_ (Const ('f':u)) (Const ('e':u))
          Var_ v   -> fromView $ Var_ v

context :: AG Singl CodesTerm (Const String) (Const Context)
context = AG $ inherit go (Const [])
  where go :: InhDefn Singl CodesTerm (Const String) (Const Context)
        go (Const u) x (Const ctx) = case sop x of
          Abs_ (SString v) _ -> fromView $ Abs_ (SString v) (Const $ (v, TyVar u) : ctx)
          _ -> copy (Const ctx) x

typing :: AG Singl CodesTerm (String :&&: Context) (Type :&&: [TyEq])
typing = AG $ synthesize go
  where go :: SynDefn Singl CodesTerm (String :&&: Context) (Type :&&: [TyEq])
        go (Pair_ u ctx) x = case sop x of
          Abs_ (SString v) (Pair_ ty cs)
            -> Pair_ (Arrow (TyVar u) ty) cs
          App_ (Pair_ ty1 cs1) (Pair_ ty2 cs2)
            -> let newEq = ty1 :=: Arrow ty2 (TyVar u)
                   newCs = newEq : cs1 ++ cs2
               in Pair_ (TyVar u) newCs
          Var_ (SString v)
            -> let Just ty = lookup v ctx
               in Pair_ ty []

checker :: AG Singl CodesTerm a (Type :&&: [TyEq])
checker = unique
          >>> arr duplicate
          >>> first context
          >>> arr swap
          >>> typing

{-
checker = proc x -> do u <- unique -< x
                       ctx <- context -< u
                       typing -< Pair u ctx
-}

lambdaT1 = t1 "a" "b"
lambdaT2 = t2 "a" "b" "c" 'd'