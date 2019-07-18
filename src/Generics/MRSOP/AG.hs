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

-- * Annotated Fixpoints

-- $annfixpoints
--
-- Annotated fixpoints are a very useful construction. Suppose the generic
-- algorithm at hand frequently requires the height of the tree being processed.
-- Instead of recomputing the height of the trees everytime we need them,
-- we can annotate the whole tree with its height at each given point.
--
-- Given an algebra that computes height at one point, assuming
-- the recursive positions have been substituted with their own heights,
--
--   > heightAlgebra :: Rep ki (Const Int) xs -> Const Int iy
--   > heightAlgebra = Const . (1+) . elimRep (const 0) getConst (maximum . (0:))
--
-- We can annotate each node with their height with the 'synthesize' function.
--
--   > synthesize heightAlgebra :: Fix ki codes ix -> AnnFix ki codes (Const Int) ix
--
-- Note how using just 'cata' would simply count the number of nodes, forgetting
-- the intermediate values.
--
--   > cata heightAlgebra :: Fix ki codes ix -> Const Int ix
--

-- | Annotated version of Fix. This is basically the 'Cofree' datatype,
-- but for n-ary functors. 
data AnnFix (ki :: kon -> *) (codes :: [[[Atom kon]]]) (phi :: Nat -> *) (n :: Nat) =
  AnnFix (phi n) (Rep ki (AnnFix ki codes phi) (Lkup n codes))

-- |Retrieves the top annotation at the current value.
getAnn :: AnnFix ki codes ann ix -> ann ix
getAnn (AnnFix a _) = a

-- |Catamorphism with access to the annotations
annCata :: IsNat ix
        => (forall iy. IsNat iy => chi iy -> Rep ki phi (Lkup iy codes) -> phi iy) -- ^
        -> AnnFix ki codes chi ix
        -> phi ix
annCata f (AnnFix a x) = f a (mapRep (annCata f) x)

-- | Forgetful natural transformation back into 'Fix'
forgetAnn :: AnnFix ki codes a ix -> Fix ki codes ix
forgetAnn (AnnFix _ rep) = Fix (mapRep forgetAnn rep)

-- | Maps over the annotations within an annotated fixpoint
mapAnn :: (IsNat ix)
       => (forall iy. chi iy -> phi iy) -- ^
       -> AnnFix ki codes chi ix
       -> AnnFix ki codes phi ix
mapAnn f = synthesizeAnn (\x _ -> f x)


-- |Annotates a tree at every node with the result
-- of the catamorphism with the supplied algebra called at
-- each node.
synthesize :: forall ki phi codes ix
            . (IsNat ix)
           => (forall iy . (IsNat iy) => Rep ki phi (Lkup iy codes) -> phi iy) -- ^
           -> Fix ki codes ix
           -> AnnFix ki codes phi ix
synthesize f = cata alg
  where
    alg :: forall iy
         . (IsNat iy)
        => Rep ki (AnnFix ki codes phi) (Lkup iy codes)
        -> AnnFix ki codes phi iy
    alg xs = AnnFix (f (mapRep getAnn xs)) xs


-- |Monadic variant of 'synthesize'
synthesizeM :: forall ki phi codes ix m
              . (Monad m , IsNat ix)
             => (forall iy  . IsNat iy => Rep ki phi (Lkup iy codes) -> m (phi iy)) -- ^
             -> Fix ki codes ix
             -> m (AnnFix ki codes phi ix)
synthesizeM f = cataM alg
  where
    alg :: forall iy
         . (IsNat iy)
        => Rep ki (AnnFix ki codes phi) (Lkup iy codes)
        -> m (AnnFix ki codes phi iy)
    alg xs = flip AnnFix xs <$> f (mapRep getAnn xs)

-- | Synthesized attributes with an algebra that has access to the annotations.
synthesizeAnn :: forall ki codes chi phi ix
               . (IsNat ix)
              => (forall iy. chi iy -> Rep ki phi (Lkup iy codes) -> phi iy) -- ^
              -> AnnFix ki codes chi ix
              -> AnnFix ki codes phi ix
synthesizeAnn f = annCata alg
  where
    alg :: forall iy
         . chi iy
        -> Rep ki (AnnFix ki codes phi) (Lkup iy codes)
        -> AnnFix ki codes phi iy
    alg ann rep = AnnFix (f ann (mapRep getAnn rep)) rep
 
