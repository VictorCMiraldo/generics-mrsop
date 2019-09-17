{-# LANGUAGE RankNTypes              #-}
{-# LANGUAGE FlexibleContexts        #-}
{-# LANGUAGE FlexibleInstances       #-}
{-# LANGUAGE FlexibleInstances       #-}
{-# LANGUAGE GADTs                   #-}
{-# LANGUAGE TypeOperators           #-}
{-# LANGUAGE DataKinds               #-}
{-# LANGUAGE PolyKinds               #-}
{-# LANGUAGE ScopedTypeVariables     #-}
{-# LANGUAGE TypeApplications        #-}
{-# LANGUAGE FunctionalDependencies  #-}
-- |Provides the main class of the library, 'Family'.
module Generics.MRSOP.Base.Class where

import Generics.MRSOP.Base.Universe
import Generics.MRSOP.Util

-- * Main Type Class 

-- |A Family consists of a list of types and a list of codes of the same length.
--  The idea is that the code of @Lkup n fam@ is @Lkup n code@.
--  We also parametrize on the interpretation of constants.
--  The class family provides primitives for performing a shallow conversion.
--  The 'deep' conversion is easy to obtain: @deep = map deep . shallow@
class Family (ki :: kon -> *) (fam :: [*]) (codes :: [[[Atom kon]]])
      | fam -> ki codes , ki codes -> fam
  where

    sfrom' :: SNat ix -> El fam ix -> Rep ki (El fam) (Lkup ix codes)
    sto'   :: SNat ix -> Rep ki (El fam) (Lkup ix codes) -> El fam ix

-- ** Shallow Conversion 

-- |A Smarter variant of 'sfrom'', since 'El' is a GADT,
--  we can extract the term-level rep of @ix@ from there.
sfrom :: forall fam ki codes ix
       . (Family ki fam codes)
      => El fam ix -> Rep ki (El fam) (Lkup ix codes)
sfrom el = sfrom' (getElSNat el) el

-- |For 'sto'' there is a similar more general combinator.
--  If @ix@ implements 'IsNat' we can cast it.
sto :: forall fam ki codes ix
     . (Family ki fam codes , IsNat ix)
    => Rep ki (El fam) (Lkup ix codes) -> El fam ix  
sto = sto' (getSNat' @ix) 

-- ** Deep Conversion
--
-- $deepConversion
--
-- The deep translation is obtained by simply
-- recursing the shallow translation at every
-- point in the (generic) tree.
--
-- @dfrom = map dfrom . sfrom@

-- |Converts an entire element of our family
--  into 
dfrom :: forall ix ki fam codes
       . (Family ki fam codes)
      => El fam ix
      -> Fix ki codes ix
dfrom = Fix . mapRep dfrom . sfrom @fam

-- |Converts an element back from a deep encoding.
--  This is the dual of 'dfrom'.
--
--  @dto = sto . map dto@
--
dto :: forall ix ki fam codes
     . (Family ki fam codes , IsNat ix)
    => Rep ki (Fix ki codes) (Lkup ix codes)
    -> El fam ix
dto = sto . mapRep (dto . unFix)

-- ** Smarter conversions into SOP

-- |Converts a type into its shallow representation.
shallow :: forall fam ty ki codes ix
         . (Family ki fam codes,
           ix ~ Idx ty fam, Lkup ix fam ~ ty, IsNat ix)
        => ty -> Rep ki (El fam) (Lkup ix codes)
shallow = sfrom . into

-- |Converts a type into its deep representation.
deep :: forall fam ty ki codes ix
      . (Family ki fam codes,
         ix ~ Idx ty fam, Lkup ix fam ~ ty, IsNat ix)
     => ty -> Fix ki codes ix
deep = dfrom . into
