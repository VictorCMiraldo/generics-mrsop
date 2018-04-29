{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
-- |Implements a rudimentary show instance for our representations.
--  We keep this isolated because the instance for @Show (Rep ki phi code)@
--  requires undecidable instances. ISolating this allows us to turn on this
--  extension for this module only.
module Generics.MRSOP.Base.Show where

import Generics.MRSOP.Base.NS
import Generics.MRSOP.Base.NP
import Generics.MRSOP.Base.Universe
import Generics.MRSOP.Util

-- https://stackoverflow.com/questions/9082642/implementing-the-show-class
instance (Show (fam k)) => Show (NA ki fam (I k)) where
  showsPrec p (NA_I v) = showParen (p > 10) $ showString "I " . showsPrec 11 v
instance (Show (ki  k)) => Show (NA ki fam (K k)) where
  showsPrec p (NA_K v) = showParen (p > 10) $ showString "K " . showsPrec 11 v

instance Show (NP p '[]) where
  show NP0 = "NP0"
instance (Show (p x), Show (NP p xs)) => Show (NP p (x : xs)) where
  showsPrec p (v :* vs)
    = let consPrec = 5
       in showParen (p > consPrec)
        $ showsPrec (consPrec + 1) v . showString " :* " . showsPrec consPrec vs

instance Show (NS p '[]) where
  show _ = error "This code is unreachable"
instance (Show (p x), Show (NS p xs)) => Show (NS p (x : xs)) where
  showsPrec p (Here  x) = showParen (p > 10) $ showString "H " . showsPrec 11 x
  showsPrec p (There x) = showString "T " . showsPrec p x

-- TODO:
-- This needs undecidable instances. We don't like undecidable instances
instance Show (NS (PoA ki phi) code) => Show (Rep ki phi code) where
  show (Rep x) = show x

instance Show (NS (PoA ki (Fix ki codes)) (Lkup ix codes))
      => Show (Fix ki codes ix)
    where
  show (Fix x) = show x
