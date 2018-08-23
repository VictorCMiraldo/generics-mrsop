{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}

-- | Attribute grammars over mutual recursive datatypes
module Generics.MRSOP.AG where

import Data.Coerce
import Data.Foldable (fold)
import Data.Functor.Const
import Data.Functor.Product
import Data.Monoid (Sum(..), (<>))
import Data.Proxy
import Generics.MRSOP.Base
import Generics.MRSOP.Util

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

mapAnn :: (forall iy. chi iy -> phi iy)
       -> AnnFix ki codes chi ix
       -> AnnFix ki codes phi ix
mapAnn f = synthesize (\_ x _ -> f x)

-- HACK. why doesn't haskell have this instance?
instance Show k => Show1 (Const k) where
  show1 (Const x) = show x

instance (Show1 f, Show1 g) => Show1 (Product f g) where
  show1 (Pair x y) = "(" ++ show1 x ++ ", " ++ show1 y ++ ")"

-- | Inherited attributes

inherit ::
     forall ki codes chi phi ix.
     (forall iy. Rep ki chi (Lkup iy codes) -> chi iy
              -> phi iy -> Rep ki phi (Lkup iy codes))
  -> phi ix
  -> AnnFix ki codes chi ix
  -> AnnFix ki codes phi ix
inherit f start (AnnFix ann rep) =
  let zipWithRep ::
           Rep ki (AnnFix ki codes chi) xs
        -> Rep ki phi xs
        -> Rep ki (AnnFix ki codes phi) xs
      zipWithRep (Rep x) (Rep y) = Rep $ zipWithNS x y
      zipWithNS ::
           NS (PoA ki (AnnFix ki codes chi)) ys
        -> NS (PoA ki phi) ys
        -> NS (PoA ki (AnnFix ki codes phi)) ys
      zipWithNS (Here x) (Here y) = Here $ zipWithNP x y
      zipWithNS (There x) (There y) = There $ zipWithNS x y
      zipWithNP ::
           PoA ki (AnnFix ki codes chi) zs
        -> PoA ki phi zs
        -> PoA ki (AnnFix ki codes phi) zs
      zipWithNP NP0 NP0 = NP0
      zipWithNP (a :* as) (b :* bs) = zipWithNA a b :* zipWithNP as bs
      zipWithNA ::
           NA ki (AnnFix ki codes chi) ws
        -> NA ki phi ws
        -> NA ki (AnnFix ki codes phi) ws
      zipWithNA (NA_I i1) (NA_I i2) = NA_I (inherit f i2 i1)
      zipWithNA (NA_K i1) (NA_K i2) = NA_K i1
      newFix = f (mapRep getAnn rep) ann start
   in AnnFix start (zipWithRep rep newFix)

data ChainAttrib phi x
  = ChainAttrib { chainStart :: forall y. phi x -> phi y
                , chainNext  :: forall y z. phi y -> phi z
                , chainEnd   :: forall y. phi y -> phi x }

type family First def xs where
  First def '[] = def
  First def (K x ': xs) = First def xs
  First def (I x ': xs) = x

type family Last def xs where
  Last def '[] = def
  Last def (K x ': xs) = Last def xs
  Last def (I x ': xs) = Last x xs

chain :: 
     forall ki codes chi phi ix.
     (forall iy. Rep ki chi (Lkup iy codes) -> chi iy -> ChainAttrib phi iy)
  -> phi ix
  -> AnnFix ki codes chi ix
  -> AnnFix ki codes phi ix
chain f start (AnnFix ann rep) =
  AnnFix finalAnn finalRep
  where chn :: ChainAttrib phi ix
        chn = f (mapRep getAnn rep) ann
        (finalAnn, finalRep) = go rep
        go   :: Rep ki (AnnFix ki codes chi) xs
             -> (phi ix, Rep ki (AnnFix ki codes phi) xs)
        go (Rep x) = Rep <$> goNS x
        goNS :: NS (PoA ki (AnnFix ki codes chi)) ys
             -> (phi ix, NS (PoA ki (AnnFix ki codes phi)) ys)
        goNS (Here  x) = let (final, reps) = goNP Proxy x (chainStart chn start)
                          in (chainEnd chn final, Here reps)
        goNS (There x) = There <$> goNS x
        goNP :: forall def zs.
                Proxy def
             -> PoA ki (AnnFix ki codes chi) zs
             -> phi (First def zs)
             -> (phi (Last def zs), PoA ki (AnnFix ki codes phi) zs)
        goNP _ NP0 t = (t, NP0)
        goNP _ ((NA_K x) :* xs) t = let (t2, xs') = goNP (Proxy :: Proxy def) xs t
                                     in (t2, (NA_K x) :* xs')
        goNP _ ((NA_I x) :* xs) t = let x' = chain f t x
                                        t1 = getAnn x'
                                        (t2, xs') = goNP (Proxy :: Proxy (First def zs)) xs (chainNext chn t1)
                                     in (t2, (NA_I x') :* xs')


-- | Synthesized attributes

synthesize ::
     forall ki codes chi phi ix.
     (forall iy. Rep ki chi (Lkup iy codes) -> chi iy   -- The other attributes
              -> Rep ki phi (Lkup iy codes) -> phi iy)
  -> AnnFix ki codes chi ix
  -> AnnFix ki codes phi ix
synthesize f = annCata alg
  where
    alg ::
         forall iy.
         Rep ki chi (Lkup iy codes)
      -> chi iy
      -> Rep ki (AnnFix ki codes phi) (Lkup iy codes)
      -> AnnFix ki codes phi iy
    alg anns ann rep = AnnFix (f anns ann (mapRep getAnn rep)) rep

-- | Chained attributes



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
sizeGeneric' :: (IsNat ix)
             => Fix ki codes ix -> AnnFix ki codes (Const (Sum Int)) ix
sizeGeneric' = synthesize (\_ _ -> sizeAlgebra)

-- | Count the number of nodes
sizeGeneric :: (IsNat ix)
            => Fix ki codes ix -> Const (Sum Int) ix
sizeGeneric = cata sizeAlgebra
