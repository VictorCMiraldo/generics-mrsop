{-# LANGUAGE TypeApplications        #-}
{-# LANGUAGE UndecidableInstances    #-}
{-# LANGUAGE RankNTypes              #-}
{-# LANGUAGE FlexibleContexts        #-}
{-# LANGUAGE FlexibleInstances       #-}
{-# LANGUAGE FlexibleInstances       #-}
{-# LANGUAGE GADTs                   #-}
{-# LANGUAGE TypeOperators           #-}
{-# LANGUAGE DataKinds               #-}
{-# LANGUAGE PolyKinds               #-}
{-# LANGUAGE ScopedTypeVariables     #-}
{-# LANGUAGE FunctionalDependencies  #-}
{-# LANGUAGE TemplateHaskell         #-}
module Generics.MRSOP.Examples.RoseTreeTH where

import Data.Function (on)

import Generics.MRSOP.Base.Internal.NS
import Generics.MRSOP.Base.Internal.NP
import Generics.MRSOP.Base.Universe
import Generics.MRSOP.Base.Class
import Generics.MRSOP.Konstants
import Generics.MRSOP.Util

import Generics.MRSOP.TH


-- * Haskell first-order RoseTrees

data Rose a = a :>: [Rose a]
  deriving Show

value1, value2 :: Rose Int
value1 = 1 :>: [2 :>: [], 3 :>: []]
value2 = 1 :>: [2 :>: []]

-- deriveFamily [t| Rose Int |]
magic ''[]
