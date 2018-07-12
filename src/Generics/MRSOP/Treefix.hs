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

-- |Kind of paths on a mutually recursive family
data Paths
  = Hole
  | End
  | Under [Paths]

type family Merge (px :: Paths) (py :: Paths) :: Paths where

data Way :: [[[Atom kon]]] -> Nat -> Paths -> * where
  WayHere  :: Way codes ix Hole
  WayThere :: Constr (Lkup i codes) n 
           -> WayNP codes (Lkup n (Lkup i codes)) paths
           -> Way codes i (Under paths)

type family Replicate (x :: k) (l :: [j]) :: [k] where
  Replicate x '[]         = '[]
  Replicate x (_ ': rest) = x ': Replicate x rest

data WayNP :: [[[Atom kon]]] -> [Atom kon] -> [Paths] -> * where
  WayNPHere  :: Way codes i path
             -> WayNP codes (I i ': prod) (path ': Replicate End prod)
  WayNPThere :: WayNP codes prod paths
             -> WayNP codes (p ': prod) (End ': paths)

--type family ExtractTypes (paths :: Paths) :: [Nat]
--  where
--    ExtractTypes (Hole ix)      = ix ': '[]
--    ExtractTypes End            = '[]
--    -- ExtractTypes (Under ix ps) = concatMap ExtractTypes ps
--    ExtractTypes (Under ix '[]) 

-- |A Tree-prefix @Tx ki fam codes i js@ specifies a path that ultimately
--  leats to @length js@ trees of the respective types inside an element
--  of type @El fam i@. In a dependently typed language, one would use
--  a notion of /subsequence/ and write a slightly more elegant version.
data Tx :: (kon -> *) -> [*] -> [[[Atom kon]]] -> Nat -> Paths -> * where
  -- |Marks the end of a path. As soon as a path ends, there is only
  --  one possible subtree it can mark.
  TxHere :: Tx ki fam codes i Hole
  -- |Marks the forking of a path by specifying a constructor
  --  and a selection of the elements of this constructor's fields
  --  to continue.
  TxPeel :: Constr (Lkup i codes) n
         -> TxNP ki fam codes (Lkup n (Lkup i codes)) paths
         -> Tx ki fam codes i (Under paths)

-- |A Tree-prefix over a product; a value pf type @TxNP ki fam codes prod js@
--  marks @length js@ subtrees of the corresponding type within a
--  product-of-atoms ('PoA') @PoA ki (El fam) prod@.
--
--  We employ several Haskell hacks here. Most notably, this datatype is
--  'fused' with a proof that 'map I js' is a subsequence of 'prod'
--
data TxNP :: (kon -> *) -> [*] -> [[[Atom kon]]] -> [Atom kon] -> [Paths] -> *
    where
  TxNPNil   :: TxNP ki fam codes '[] '[]
  TxNPPath  :: Tx ki fam codes i ys
            -> TxNP ki fam codes prod yss
            -> TxNP ki fam codes (I i ': prod) (ys ': yss)
  TxNPSolid :: NA ki (El fam) at
            -> TxNP ki fam codes prod yss
            -> TxNP ki fam codes (at ': prod) (End ': yss)

{-

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

-- |Creates the final tree-fix; that is: the one with zero holes that
--  matches the whole element.
--
-- TODO: think about TxNPSolid; should it force the atom
--       to be an opaque type?
--       If so, then @Tx ki dam codes ix '[]@ is just like a deep representation
--       We'd then have operations to extract subtrees from there.
finalTx :: (Family ki fam codes)
        => El fam ix -> Tx ki fam codes ix '[]
finalTx x | Tag cx px <- sop (sfrom x) = TxPeel cx (finalTxNP px)
  where
    finalTxNP :: (Family ki fam codes)
              => PoA ki (El fam) prod
              -> TxNP ki fam codes prod '[]
    finalTxNP NP0            = TxNPNil
    finalTxNP (NA_I a :* as) = TxNPPath  (finalTx a) (finalTxNP as)
    finalTxNP (NA_K a :* as) = TxNPSolid (NA_K a)    (finalTxNP as)
  
-}
