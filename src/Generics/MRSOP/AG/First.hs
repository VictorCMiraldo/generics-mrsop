{-# LANGUAGE Arrows              #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PolyKinds           #-}
module Generics.MRSOP.AG.First where

import Prelude hiding ((.), id)
import Control.Category
import Control.Arrow
import Data.Coerce
import Data.Foldable (fold)
import Data.Functor.Const
import Data.Proxy
import Data.Monoid (Sum(..), (<>))

import Generics.MRSOP.Base
import Generics.MRSOP.Util
import Generics.MRSOP.AG

newtype AG ki codes a b
  = AG { unAG :: forall ix. AnnFix ki codes (Const a) ix -> AnnFix ki codes (Const b) ix }

instance Category (AG ki codes) where
  id = AG id
  (AG a) . (AG b) = AG (a . b)

overConst :: (a -> b) -> Const a t -> Const b t
overConst f (Const x) = Const (f x)

overConst2 :: (a -> b -> c) -> Const a t -> Const b t -> Const c t
overConst2 f (Const x) (Const y) = Const (f x y)

instance Arrow (AG ki codes) where
  arr f = AG $ mapAnn (overConst f)
  first (AG ag) = AG $ \x ->
                        zipAnn (overConst2 (,))
                               (ag (mapAnn (overConst fst) x))
                                   (mapAnn (overConst snd) x)

instance ArrowLoop (AG ki codes) where
  loop (AG ag) = AG $ \b -> let bd = zipAnn (overConst2 (,)) b d
                                cd = ag bd
                                c = mapAnn (overConst fst) cd
                                d = mapAnn (overConst snd) cd
                             in c

voidAnn :: IsNat ix => Fix ki codes ix -> AnnFix ki codes (Const ()) ix
voidAnn = synthesize (\_ _ _ -> Const ())

runAG :: IsNat ix => AG ki codes () r -> Fix ki codes ix -> AnnFix ki codes (Const r) ix
runAG (AG ag) = ag . voidAnn

inh :: forall ki codes a b.
       (forall iy. Proxy iy -> Rep ki (Const a) (Lkup iy codes) -> a
                -> b -> Rep ki (Const b) (Lkup iy codes))
    -> b
    -> AG ki codes a b
inh f b = AG $ inherit go (Const b)
  where go :: forall iw. Rep ki (Const a) (Lkup iw codes) -> Const a iw 
                      -> Const b iw -> Rep ki (Const b) (Lkup iw codes)
        go skeleton (Const a) (Const b) = f (Proxy :: Proxy iw) skeleton a b

inh_ :: forall ki codes a b.
       (forall iy. Proxy iy -> Rep ki (Const a) (Lkup iy codes) -> b
                   -> Rep ki (Const b) (Lkup iy codes))
    -> b
    -> AG ki codes a b
inh_ f = inh (\p skeleton _ attrib -> f p skeleton attrib)

syn :: forall ki codes a b.
       (forall iy. Proxy iy -> a -> Rep ki (Const b) (Lkup iy codes) -> b)
    -> AG ki codes a b
syn f = AG $ synthesize go
  where go :: forall iw. Rep ki (Const a) (Lkup iw codes) -> Const a iw
                      -> Rep ki (Const b) (Lkup iw codes) -> Const b iw
        go _ (Const a) r = Const $ f (Proxy :: Proxy iw) a r

syn_ :: forall ki codes a b.
        (forall iy. Proxy iy -> Rep ki (Const b) (Lkup iy codes) -> b)
     -> AG ki codes a b
syn_ f = syn (\p _ -> f p)

sizeGenericAG :: AG ki codes a (Sum Int)
sizeGenericAG = syn_ sizeAlgebraAG
  where sizeAlgebraAG :: p -> Rep ki (Const (Sum Int)) xs -> Sum Int
        sizeAlgebraAG _ = (1 <>) . getConst . elimRep mempty coerce fold

depthGenericAG :: AG ki codes a Int
depthGenericAG = inh_ (\_ r n -> mapRep (const (Const (n+1))) r) 0

sizeTwiceDepth :: AG ki codes a (Sum Int, Int)
sizeTwiceDepth = proc x -> do r <- sizeGenericAG -< x
                              d <- depthGenericAG -< x
                              returnA -< (r + r, d)