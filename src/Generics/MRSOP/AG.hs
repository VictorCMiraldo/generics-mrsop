{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs               #-}

-- | Attribute grammars over mutual recursive datatypes
module Generics.MRSOP.AG where

import Data.Functor.Const
import Generics.MRSOP.Base

-- | Annotated version of Fix.   This is basically the 'Cofree' datatype,
-- but for n-ary functors
data AnnFix (ki :: kon -> *) (codes :: [[[Atom kon]]]) (phi :: Nat -> *) (n :: Nat) =
  AnnFix (phi n)
         (Rep ki (AnnFix ki codes phi) (Lkup n codes))

getAnn :: AnnFix ki codes ann ix -> ann ix
getAnn (AnnFix a _) = a

annCata :: IsNat ix
        => (forall iy. IsNat iy => chi iy -> Rep ki phi (Lkup iy codes) -> phi iy)
        -> AnnFix ki codes chi ix
        -> phi ix
annCata f (AnnFix a x) = f a (mapRep (annCata f) x)

-- | Forget the annotations
forgetAnn :: AnnFix ki codes a ix -> Fix ki codes ix
forgetAnn (AnnFix _ rep) = Fix (mapRep forgetAnn rep)

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
    zipWithNS _         _         = error "Can't have this!"
    zipWithNP :: PoA ki (AnnFix ki codes phi1) zs
              -> PoA ki (AnnFix ki codes phi2) zs
              -> PoA ki (AnnFix ki codes phi3) zs
    zipWithNP NP0 NP0 = NP0
    zipWithNP (a :* as) (b :* bs) = zipWithNA a b :* zipWithNP as bs
    zipWithNA :: NA ki (AnnFix ki codes phi1) ws
              -> NA ki (AnnFix ki codes phi2) ws
              -> NA ki (AnnFix ki codes phi3) ws
    zipWithNA (NA_I u1) (NA_I u2) = NA_I (zipAnn f u1 u2)
    zipWithNA (NA_K i1) (NA_K _)  = NA_K i1  -- Should be the same!

mapAnn :: (IsNat ix)
       => (forall iy. chi iy -> phi iy)
       -> AnnFix ki codes chi ix
       -> AnnFix ki codes phi ix
mapAnn f = synthesizeAnn (\x _ -> f x)

-- | Inherited attributes
inheritAnn :: forall ki codes chi phi ix
            . (forall iy. chi iy -> Rep ki (Const ()) (Lkup iy codes)
                       -> phi iy -> Rep ki phi (Lkup iy codes))
           -> phi ix
           -> AnnFix ki codes chi ix
           -> AnnFix ki codes phi ix
inheritAnn f start (AnnFix ann rep) =
  let newFix = f ann (mapRep (const (Const ())) rep) start
      zipWithRep ::
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
      zipWithNS _ _ = error "Can't have this"
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
      zipWithNA (NA_I i1) (NA_I i2) = NA_I (inheritAnn f i2 i1)
      zipWithNA (NA_K i1) (NA_K _)  = NA_K i1
   in AnnFix start (zipWithRep rep newFix)

inherit :: forall ki phi codes ix
         . (forall iy. Rep ki (Const ()) (Lkup iy codes) -> phi iy
                    -> Rep ki phi (Lkup iy codes))
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
      zipWithNS _ _ = error "Can't have this"
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
      zipWithNA (NA_K i1) (NA_K _)  = NA_K i1
   in AnnFix start (zipWithRep rep newFix)

-- | Synthesized attributes
synthesizeAnn :: forall ki codes chi phi ix
               . (IsNat ix)
              => 
                 (forall iy. chi iy -> Rep ki phi (Lkup iy codes) -> phi iy)
              -> AnnFix ki codes chi ix
              -> AnnFix ki codes phi ix
synthesizeAnn f = annCata alg
  where
    alg :: forall iy
         . chi iy
        -> Rep ki (AnnFix ki codes phi) (Lkup iy codes)
        -> AnnFix ki codes phi iy
    alg ann rep = AnnFix (f ann (mapRep getAnn rep)) rep
    

-- |Example of using 'synthesize' to annotate a tree with its size
-- at every node.
--
--   > sizeAlgebra :: Rep ki (Const (Sum Int)) xs -> Const (Sum Int) iy
--   > sizeAlgebra = (Const 1 <>) . monoidAlgebra
--
-- Annotate each node with the number of subtrees
--
--   > sizeGeneric' :: (IsNat ix)
--   >              => Fix ki codes ix -> AnnFix ki codes (Const (Sum Int)) ix
--   > sizeGeneric' = synthesize sizeAlgebra
--
-- Note how using just 'cata' will simply count the number of nodes
--
--   > sizeGeneric :: (IsNat ix)
--   >             => Fix ki codes ix -> Const (Sum Int) ix
--   > sizeGeneric = cata sizeAlgebra
--
synthesize :: forall ki phi codes ix
            . (IsNat ix)
           => (forall iy . (IsNat iy) => Rep ki phi (Lkup iy codes) -> phi iy)
           -> Fix ki codes ix
           -> AnnFix ki codes phi ix
synthesize f = cata alg
  where
    alg :: forall iy
         . (IsNat iy)
        => Rep ki (AnnFix ki codes phi) (Lkup iy codes)
        -> AnnFix ki codes phi iy
    alg xs = AnnFix (f (mapRep getAnn xs)) xs

