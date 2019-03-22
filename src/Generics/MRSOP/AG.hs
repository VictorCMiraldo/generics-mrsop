{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs               #-}

-- | Attribute grammars over mutual recursive datatypes
module Generics.MRSOP.AG where

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

mapAnn :: (IsNat ix)
       => (forall iy. chi iy -> phi iy)
       -> AnnFix ki codes chi ix
       -> AnnFix ki codes phi ix
mapAnn f = synthesizeAnn (\x _ -> f x)

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

