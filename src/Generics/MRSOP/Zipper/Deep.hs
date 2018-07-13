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
import Control.Monad (guard)
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


-- | Given a product with a hole in it, and an element, get back
-- a product
--
-- dual of 'removeNPHole'
fillNPHole ::
     IsNat ix
  => Fix ki codes ix
  -> NPHole ki fam codes ix xs
  -> PoA ki (Fix ki codes) xs
fillNPHole x (H xs) = NA_I x :* xs
fillNPHole x (T y ys) = y :* fillNPHole x ys


-- | Given a product with a hole in it, and a product, get back an element
-- dual of 'fillNPHole'
--
-- They are a prism together
removeNPHole ::
     (Eq1 ki, IsNat ix)
  => PoA ki (Fix ki codes) xs
  -> NPHole ki fam codes ix xs
  -> Maybe (Fix ki codes ix)
removeNPHole (NA_I x :* xs) (H ys) = do
  guard $ eq1 xs ys
  Just x
removeNPHole xs (T y ys) = _

