{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE Arrows #-}

-- | Attribute grammars over mutual recursive datatypes
module Generics.MRSOP.AG where

import Data.Functor.Const
import Data.Coerce
import Data.Foldable (fold)
import Data.Monoid (Sum(..), (<>))
import Generics.MRSOP.Base
import Generics.MRSOP.Util

import Prelude hiding ((.), id)
import Control.Category
import Control.Arrow
import Data.Proxy

newtype AG ki codes a b
  = AG { unAG :: forall ix. AnnFix ki codes (Const a) ix -> AnnFix ki codes (Const b) ix }

instance Category (AG ki codes) where
  id = AG id
  (AG a) . (AG b) = AG (a . b)

instance Arrow (AG ki codes) where
  arr f = AG $ synthesizeAnn (\(Const x) _ -> Const (f x))
  first (AG ag) = AG $ \x ->
                        zipAnn (\(Const b) (Const d) -> Const (b,d))
                               (ag (synthesizeAnn (\(Const (a,d)) _ -> Const a) x))
                               (synthesizeAnn (\(Const (a,d)) _ -> Const d) x)

voidAnn :: Fix ki codes ix -> AnnFix ki codes (Const ()) ix
voidAnn = synthesize (\_ -> Const ())

runAG :: AG ki codes () r -> Fix ki codes ix -> AnnFix ki codes (Const r) ix
runAG (AG ag) = ag . voidAnn

zipAnn :: forall phi1 phi2 phi3 ki codes ix.
          (forall iy. phi1 iy -> phi2 iy -> phi3 iy)
       -> AnnFix ki codes phi1 ix
       -> AnnFix ki codes phi2 ix
       -> AnnFix ki codes phi3 ix
zipAnn f (AnnFix a1 t1) (AnnFix a2 t2) = AnnFix (f a1 a2) (zipWithRep t1 t2)
  where
    zipWithRep :: Rep ki (AnnFix ki codes phi1) xs
               -> Rep ki (AnnFix ki codes phi2) xs
               -> Rep ki (AnnFix ki codes phi3) xs
    zipWithRep (Rep x) (Rep y) = Rep $ zipWithNS x y
    zipWithNS :: NS (PoA ki (AnnFix ki codes phi1)) ys
              -> NS (PoA ki (AnnFix ki codes phi2)) ys
              -> NS (PoA ki (AnnFix ki codes phi3)) ys
    zipWithNS (Here x) (Here y)   = Here $ zipWithNP x y
    zipWithNS (There x) (There y) = There $ zipWithNS x y
    zipWithNP :: PoA ki (AnnFix ki codes phi1) zs
              -> PoA ki (AnnFix ki codes phi2) zs
              -> PoA ki (AnnFix ki codes phi3) zs
    zipWithNP NP0 NP0 = NP0
    zipWithNP (a :* as) (b :* bs) = zipWithNA a b :* zipWithNP as bs
    zipWithNA :: NA ki (AnnFix ki codes phi1) ws
              -> NA ki (AnnFix ki codes phi2) ws
              -> NA ki (AnnFix ki codes phi3) ws
    zipWithNA (NA_I t1) (NA_I t2) = NA_I (zipAnn f t1 t2)
    zipWithNA (NA_K i1) (NA_K i2) = NA_K i1  -- Should be the same!

instance Show k => Show1 (Const k) where
  show1 (Const x) = "(Const " ++ show x ++ ")"

inherit ::
     forall ki phi codes ix.
     (forall iy. Rep ki (Const ()) (Lkup iy codes) -> phi iy -> Rep ki phi (Lkup iy codes))
  -> phi ix
  -> Fix ki codes ix
  -> AnnFix ki codes phi ix
inherit f start (Fix rep) =
  let newFix = (f (mapRep (const (Const ())) rep) start)
      zipWithRep ::
           Rep ki (Fix ki codes) xs
        -> Rep ki phi xs
        -> Rep ki (AnnFix ki codes phi) xs
      zipWithRep (Rep x) (Rep y) = Rep $ zipWithNS x y
      zipWithNS ::
           NS (PoA ki (Fix ki codes)) ys
        -> NS (PoA ki phi) ys
        -> NS (PoA ki (AnnFix ki codes phi)) ys
      zipWithNS (Here x) (Here y) = Here $ zipWithNP x y
      zipWithNS (There x) (There y) = There $ zipWithNS x y
      zipWithNP ::
           PoA ki (Fix ki codes) zs
        -> PoA ki phi zs
        -> PoA ki (AnnFix ki codes phi) zs
      zipWithNP NP0 NP0 = NP0
      zipWithNP (a :* as) (b :* bs) = zipWithNA a b :* zipWithNP as bs
      zipWithNA ::
           NA ki (Fix ki codes) ws
        -> NA ki phi ws
        -> NA ki (AnnFix ki codes phi) ws
      zipWithNA (NA_I i1) (NA_I i2) = NA_I (inherit f i2 i1)
      zipWithNA (NA_K i1) (NA_K i2) = NA_K i1
   in AnnFix start (zipWithRep rep newFix)

-- inh   ~ syn a -> a

-- AG ki codes phi = forall ix. Fix ki codes ix -> AnnFix ki codes phi ix
--
-- (forall y. phi1 y -> phi2 y -> phi3 y) -> AG ki codes phi1 -> AG ki codes phi2 -> AG ki codes phi3
--
-- | Synthesized attributes

synthesizeAnn ::
     forall ki codes chi phi ix.
     (forall iy. chi iy -> Rep ki phi (Lkup iy codes) -> phi iy)
  -> AnnFix ki codes chi ix
  -> AnnFix ki codes phi ix
synthesizeAnn f = annCata alg
  where
    alg ::
         forall iy.
         chi iy
      -> Rep ki (AnnFix ki codes phi) (Lkup iy codes)
      -> AnnFix ki codes phi iy
    alg ann rep = AnnFix (f ann (mapRep getAnn rep)) rep
    

synthesize ::
     forall ki phi codes ix.
     (forall iy. Rep ki phi (Lkup iy codes) -> phi iy)
  -> Fix ki codes ix
  -> AnnFix ki codes phi ix
synthesize f = cata alg
  where
    alg ::
         forall iy.
         Rep ki (AnnFix ki codes phi) (Lkup iy codes)
      -> AnnFix ki codes phi iy
    alg xs = AnnFix (f (mapRep getAnn xs)) xs

syn :: forall ki codes a b.
       (forall iy. Proxy iy -> a -> Rep ki (Const b) (Lkup iy codes) -> b)
    -> AG ki codes a b
syn f = AG $ synthesizeAnn go
  where go :: forall iw. Const a iw -> Rep ki (Const b) (Lkup iw codes) -> Const b iw
        go (Const a) r = Const $ f (Proxy :: Proxy iw) a r

syn_ :: forall ki codes a b.
        (forall iy. Proxy iy -> Rep ki (Const b) (Lkup iy codes) -> b)
     -> AG ki codes a b
syn_ f = syn (\p _ r -> f p r)

monoidAlgebra :: Monoid m => Rep ki (Const m) xs -> Const m iy
monoidAlgebra = elimRep mempty coerce fold

-- If haskell had semirings in base, or edward kmett had a package for it
-- we could do :
-- semiringAlgebra :: Semiring w => Rep ki (Const w) xs -> Const w iy
-- semiringAlgebra = (one <>) . monoidAlgebra
--
-- sizeAlgebra :: Rep ki (Const (Sum Int)) xs -> Const (Sum Int) iy
-- sizeAlgebra = semiringAlgebra

sizeAlgebra :: Rep ki (Const (Sum Int)) xs -> Const (Sum Int) iy
sizeAlgebra = (Const 1 <>) . monoidAlgebra

-- | Annotate each node with the number of subtrees
sizeGeneric' :: Fix ki codes ix -> AnnFix ki codes (Const (Sum Int)) ix
sizeGeneric' = synthesize sizeAlgebra

sizeGeneric'' :: AG ki codes a (Sum Int)
sizeGeneric'' = syn_ sizeAlgebra''
  where sizeAlgebra'' :: p -> Rep ki (Const (Sum Int)) xs -> Sum Int
        sizeAlgebra'' _ = (1 <>) . getConst . elimRep mempty coerce fold

sizeTwice :: AG ki codes a (Sum Int)
sizeTwice = proc x -> do r <- sizeGeneric'' -< x
                         returnA -< r + r

-- | Count the number of nodes
sizeGeneric :: Fix ki codes ix -> Const (Sum Int) ix
sizeGeneric = cata sizeAlgebra


