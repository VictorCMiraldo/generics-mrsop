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


-- |Example of using 'synthesize' to annotate a tree with its size
-- at every node.
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
    
-- * Monadic Variants

-- $monadicvariants
--
-- These will rarely be needed. And are not /catamorphisms/ or /synthesized attributes/
-- per se, but have shown to be incredibly useful in some other internal projects
-- where we use /generics-mrsop/. We are leaving them in the library in case
-- they see some other usecases.

-- |Generalized catamorphism, with an auxiliary function that can
-- modify the result or perform a monadic action based on the value 
-- being processed. Care must be taken to /not/ consume the value in the
-- first argument.
cataM' :: (Monad m , IsNat ix)
       => (forall iy a. IsNat iy => Fix ki codes iy -> m a -> m a) -- ^
       -> (forall iy  . IsNat iy => Rep ki phi (Lkup iy codes) -> m (phi iy))
       -> Fix ki codes ix
       -> m (phi ix)
cataM' p f xo@(Fix x) = mapRepM (p xo . cataM' p f) x >>= f

-- |Synthesizes an annotated fixpoint based on 'cataM''
synthesizeM' :: forall ki phi codes ix m
              . (Monad m , IsNat ix)
             => (forall iy a. IsNat iy => Fix ki codes iy -> m a -> m a) -- ^
             -> (forall iy  . IsNat iy => Rep ki phi (Lkup iy codes) -> m (phi iy))
             -> Fix ki codes ix
             -> m (AnnFix ki codes phi ix)
synthesizeM' p f = cataM' p alg
  where
    alg :: forall iy
         . (IsNat iy)
        => Rep ki (AnnFix ki codes phi) (Lkup iy codes)
        -> m (AnnFix ki codes phi iy)
    alg xs = flip AnnFix xs <$> f (mapRep getAnn xs)
