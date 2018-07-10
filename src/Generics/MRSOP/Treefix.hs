{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
-- |Provides the notion of typed tree-prefix
--  for out universe.
module Generics.MRSOP.Treefix where

import Data.Type.Equality

import Generics.MRSOP.Util hiding (Cons , Nil)
import Generics.MRSOP.Base

-- |A Tree-prefix @Tx ki fam codes i js@ specifies a path that ultimately
--  leats to @length js@ trees of the respective types inside an element
--  of type @El fam i@. In a dependently typed language, one would use
--  a notion of /subsequence/ and write a slightly more elegant version.
data Tx :: (kon -> *) -> [*] -> [[[Atom kon]]] -> Nat -> [Nat] -> * where
  -- |Marks the end of a path. As soon as a path ends, there is only
  --  one possible subtree it can mark.
  TxHere :: Tx ki fam codes i (i ': '[])
  -- |Marks the forking of a path by specifying a constructor
  --  and a selection of the elements of this constructor's fields
  --  to continue.
  TxPeel :: Constr (Lkup i codes) n
         -> TxNP ki fam codes (Lkup n (Lkup i codes)) ys
         -> Tx ki fam codes i ys

-- |A Tree-prefix over a product; a value pf type @TxNP ki fam codes prod js@
--  marks @length js@ subtrees of the corresponding type within a
--  product-of-atoms ('PoA') @PoA ki (El fam) prod@.
--
--  We employ several Haskell hacks here. Most notably, this datatype is
--  'fused' with a proof that 'map I js' is a subsequence of 'prod'
--
data TxNP :: (kon -> *) -> [*] -> [[[Atom kon]]] -> [Atom kon] -> [Nat] -> *
    where
  TxNPNil   :: TxNP ki fam codes '[] '[]
  TxNPPath  :: Tx ki fam codes i ys
            -> TxNP ki fam codes prod yss
            -> TxNP ki fam codes (I i ': prod) (ys :++: yss)
  TxNPSolid :: NA ki (El fam) at
            -> TxNP ki fam codes prod yss
            -> TxNP ki fam codes (at ': prod) yss

-- |Given a treefix ('Tx') and an element, try to return all the
--  subtrees in the specified paths.
select :: (Family ki fam codes , Eq1 ki , Eq1 (El fam))
       => Tx ki fam codes ix iys -> El fam ix -> Maybe (NP (El fam) iys)
select TxHere          x = Just (x :* NP0)
select (TxPeel c txnp) x = match c (sfrom x) >>= selectNP txnp 

-- |Auxiliary function to 'select'
selectNP :: (Family ki fam codes, Eq1 ki , Eq1 (El fam))
         => TxNP ki fam codes prod iys
         -> PoA ki (El fam) prod
         -> Maybe (NP (El fam) iys)
selectNP TxNPNil NP0 = Just NP0
selectNP (TxNPSolid el txnp) (a :* poa)
  | eqNA eq1 eq1 el a = selectNP txnp poa
  | otherwise         = Nothing
selectNP (TxNPPath  tx txnp) (NA_I a :* poa)
  = appendNP <$> select tx a <*> selectNP txnp poa
