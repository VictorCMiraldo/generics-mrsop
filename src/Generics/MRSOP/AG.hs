{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}

-- | Attribute grammars over mutual recursive datatypes
module Generics.MRSOP.AG where

import Data.Functor.Const
import Data.Coerce
import Data.Foldable (fold)
import Data.Monoid (Sum(..), (<>))
import Generics.MRSOP.Base
import Generics.MRSOP.Util

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

-- | Count the number of nodes
sizeGeneric :: Fix ki codes ix -> Const (Sum Int) ix
sizeGeneric = cata sizeAlgebra

