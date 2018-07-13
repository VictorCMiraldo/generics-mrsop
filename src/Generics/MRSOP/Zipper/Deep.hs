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
-- | Provides one-hole contexts for our universe, but over
-- deep encoded datatypes. These are a bit easier to use
-- computationally
module Generics.MRSOP.Zipper.Deep where
import Data.Type.Equality

import Generics.MRSOP.Util hiding (Cons , Nil)
import Generics.MRSOP.Base



data Ctxs (ki :: kon -> *) (fam :: [*]) (codes :: [[[Atom kon]]]) :: Nat -> Nat -> * where
  Nil :: Ctxs ki fam codes ix ix
  Cons
    :: (IsNat ix, IsNat a, IsNat b)
    => Ctx ki fam codes (Lkup ix codes) b
    -> Ctxs ki fam codes a ix
    -> Ctxs ki fam codes a b

data Ctx (ki :: kon -> *) (fam :: [*]) (codes :: [[[Atom kon]]]) :: [[Atom kon]] -> Nat -> * where
  Ctx
    :: Constr c n -> NPHole ki fam codes ix (Lkup n c) -> Ctx ki fam codes c ix

data NPHole (ki :: kon -> *) (fam :: [*]) (codes :: [[[Atom kon]]]) :: Nat -> [Atom kon] -> * where
  H :: PoA ki (Fix ki codes) xs -> NPHole ki fam codes ix (I ix ': xs)
  T
    :: NA ki (Fix ki codes) x
    -> NPHole ki fam codes ix xs
    -> NPHole ki fam codes ix (x ': xs)
