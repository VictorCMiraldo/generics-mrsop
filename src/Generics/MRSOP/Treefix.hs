{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE UndecidableInstances #-}
-- |Provides the notion of typed tree-prefix
--  for out universe.
module Generics.MRSOP.Treefix where

import Data.Proxy
import Data.Type.Equality
import Data.Kind (Type)

import Generics.MRSOP.Util hiding (Cons , Nil)
import Generics.MRSOP.Base

-- |Forgetful version of 'Path', that drops the indexes so we do not
--  have to use @TypeInType@
data PathU :: Type where
  EndU  :: PathU
  HoleU :: Nat -> PathU
  ForkU :: { pathType   :: Nat  
           , pathConstr :: Nat 
           , pathFields :: [PathU]
           } -> PathU

type family PathTypes (p :: PathU) :: [Nat] where
  PathTypes EndU           = '[]
  PathTypes (HoleU i)      = i ': '[]
  PathTypes (ForkU i c ps) = PathTypesNP ps

type family PathTypesNP (ps :: [PathU]) :: [Nat] where
  PathTypesNP '[]       = '[]
  PathTypesNP (p ': ps) = PathTypes p :++: PathTypesNP ps

data PathLeaves :: (Nat -> Type) -> PathU -> Type where
  EndL  :: PathLeaves f EndU
  HoleL :: f i -> PathLeaves f (HoleU i)
  ForkL :: NP (PathLeaves f) ps
        -> PathLeaves f (ForkU i c ps)

-- |A value @p : Path codes a@ specifies a path of constructors
--  inside an inhabitant of @NA ki (Fix codes) a@.
data Path (codes :: [[[Atom kon]]]) (a :: Atom kon) (p :: PathU) :: Type where
  End  :: Path codes (K k) EndU
  Hole :: (IsNat i)
       => Path codes (I i) (HoleU i)
  Fork :: (IsNat ctr , IsNat i)
       => Constr (Lkup i codes) ctr
       -> PathNP codes (Lkup ctr (Lkup i codes)) ps
       -> Path codes (I i) (ForkU i ctr ps)

-- |A value @w : Way codes a@ specifies a pat
--  with a single hole. It's different from a zipper
--  since it carries no data.
data Way :: [[[Atom kon]]] -> Atom kon -> Type where
  HoleW  :: Way codes (I i)
  Follow :: (IsNat ctr , IsNat i)
         => Constr (Lkup i codes) ctr
         -> NS (Way codes) (Lkup ctr (Lkup i codes))
         -> Way codes (I i)

instance Show (Way codes a) where
  show HoleW = "HoleW"
  show (Follow c ns)
    = let (n , str) = go ns
       in show c ++ "{" ++ show n ++ "}(" ++ str ++ ")"
    where
      go :: NS (Way codes) s -> (Int , String)
      go (Here x) = (0 , show x)
      go (There y) = (1+) *** id $ go y

data PathE :: [[[Atom kon]]] -> Nat -> Type where
  PathE :: Path codes (I i) p -> PathE codes i

data PathNP (codes :: [[[Atom kon]]]) (prod :: [Atom kon]) (ps :: [PathU]) :: Type where
  PNPNil  :: PathNP codes '[] '[]
  PNPCons :: Path   codes a  p
          -> PathNP codes as ps
          -> PathNP codes (a ': as) (p ': ps)
 
-- |Forgetful map from 'Path' to 'PathU'
pathFgt :: Path codes a p -> PathU
pathFgt End  = EndU
pathFgt f@(Hole) = HoleU (snat2Nat $ getSNat (tyProxy f))
  where
    tyProxy :: Path codes (I i) p -> Proxy i
    tyProxy _ = Proxy
pathFgt f@(Fork ctr np)
  = ForkU (snat2Nat $ getSNat (tyProxy f))
          (snat2Nat $ getSNat (ctrProxy ctr))
          (pathFgtNP np)
  where
    ctrProxy :: Constr l ctr -> Proxy ctr
    ctrProxy _ = Proxy

    tyProxy :: Path codes (I i) p -> Proxy i
    tyProxy _ = Proxy

    pathFgtNP :: PathNP codes prod ps -> [PathU]
    pathFgtNP PNPNil = []
    pathFgtNP (PNPCons p ps) = pathFgt p : pathFgtNP ps

-- |A Tree-prefix @Tx ki fam codes i js@ specifies a path that ultimately
--  leats to @length js@ trees of the respective types inside an element
--  of type @El fam i@. In a dependently typed language, one would use
--  a notion of /subsequence/ and write a slightly more elegant version.
data Tx :: (kon -> *) -> [*] -> [[[Atom kon]]] -> Nat -> PathU -> * where
  -- |Marks the end of a path. As soon as a path ends, there is only
  --  one possible subtree it can mark.
  TxHere :: Tx ki fam codes i (HoleU i)
  -- |Marks the forking of a path by specifying a constructor
  --  and a selection of the elements of this constructor's fields
  --  to continue.
  TxPeel :: Constr (Lkup i codes) n
         -> TxNP ki fam codes (Lkup n (Lkup i codes)) paths
         -> Tx ki fam codes i (ForkU i n paths)

-- |A Tree-prefix over a product; a value pf type @TxNP ki fam codes prod js@
--  marks @length js@ subtrees of the corresponding type within a
--  product-of-atoms ('PoA') @PoA ki (El fam) prod@.
--
--  We employ several Haskell hacks here. Most notably, this datatype is
--  'fused' with a proof that 'map I js' is a subsequence of 'prod'
--
data TxNP :: (kon -> *) -> [*] -> [[[Atom kon]]] -> [Atom kon] -> [PathU] -> *
    where
  TxNPNil   :: TxNP ki fam codes '[] '[]
  TxNPPath  :: (IsNat i)
            => Tx ki fam codes i ys
            -> TxNP ki fam codes prod yss
            -> TxNP ki fam codes (I i ': prod) (ys ': yss)
  TxNPSolid :: ki k
            -> TxNP ki fam codes prod yss
            -> TxNP ki fam codes (K k ': prod) (EndU ': yss) 

visit :: (Family ki fam codes)
      => El fam i -> Path codes (I i) p -> Maybe (Tx ki fam codes i p)
visit el Hole        = return TxHere
visit el (Fork c ps) = do
  fields <- match c (sfrom el)
  txno   <- visitNP fields ps
  return (TxPeel c txno)
  where
    visitNP :: (Family ki fam codes)
            => PoA ki (El fam) prod
            -> PathNP codes prod ps 
            -> Maybe (TxNP ki fam codes prod ps)
    visitNP NP0 PNPNil = Just TxNPNil
    visitNP (NA_K k :* as) (PNPCons End ps)
      = TxNPSolid k <$> visitNP as ps
    visitNP (NA_I v :* as) (PNPCons pv ps)
      = TxNPPath <$> visit v pv <*> visitNP as ps

txInj :: (Family ki fam codes, IsNat ix)
      => Tx ki fam codes ix p
      -> PathLeaves (El fam) p
      -> El fam ix
txInj TxHere        (HoleL el)  = el
txInj (TxPeel c ps) (ForkL els) = sto $ inj c (txnpInj ps els)
  where
    txnpInj :: (Family ki fam codes)
            => TxNP ki fam codes prod ps
            -> NP (PathLeaves (El fam)) ps
            -> PoA ki (El fam) prod
    txnpInj TxNPNil            els
      = NP0
    txnpInj (TxNPSolid k rest) (EndL :* els)
      = NA_K k :* txnpInj rest els
    txnpInj (TxNPPath  v rest) (els  :* dls)
      = NA_I (txInj v els) :* txnpInj rest dls

{-

-- |Kind of paths on a mutually recursive family
data Paths
  = Hole
  | End
  | Under [Paths]


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

type family (px :: Paths) :&: (py :: Paths) :: Paths where

walkTo :: Way codes i path'
       -> Tx ki fam codes i path
       -> Maybe (Tx ki fam codes i (path :&: path'))
walkTo WayHere tx            = _
walkTo (WayThere c wayNP) tx = _

-}
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
