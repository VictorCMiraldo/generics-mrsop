{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE ScopedTypeVariables  #-}
-- | Re-exports everything from under @Generics.MRSOP.Base@ and
-- @Generics.MRSOP.Util@:
--
--  - "Generics.MRSOP.Base.NS"
--  - "Generics.MRSOP.Base.NP"
--  - "Generics.MRSOP.Base.Universe"
--  - "Generics.MRSOP.Base.Class"
--  - "Generics.MRSOP.Base.Metadata"
--  - "Generics.MRSOP.Base.Combinators"
--  - "Generics.MRSOP.Util"
--
-- For a lightweight example on how to use the library, please refer to "Generics.MRSOP.Examples.RoseTree"
-- or to the full <https://victorcmiraldo.github.io/data/tyde2018_draft.pdf paper> for a more in-depth explanation 
module Generics.MRSOP.Base (module Export) where

import Generics.MRSOP.Base.NS          as Export
import Generics.MRSOP.Base.NP          as Export
import Generics.MRSOP.Base.Universe    as Export
import Generics.MRSOP.Base.Class       as Export
import Generics.MRSOP.Base.Metadata    as Export
import Generics.MRSOP.Base.Combinators as Export
import Generics.MRSOP.Util             as Export

