{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeApplications        #-}
{-# LANGUAGE RankNTypes              #-}
{-# LANGUAGE EmptyCase               #-}
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
{-# LANGUAGE LambdaCase              #-}

module Generics.MRSOP.Examples.Bug where

import Generics.MRSOP.Base
import Generics.MRSOP.Opaque
import Generics.MRSOP.Util
import Generics.MRSOP.TH

-- The more data types you add that are mutually recursive, the more memory it uses
-- Currently, this one uses around 10GiB to typecheck
data A 
   = A1 A B C D E F G
   | A2 A B C D E F G
   | A3 A B C D E F G
   | A4 A B C D E F G
   | A5 A B C D E F G
   | A6 A B C D E F G
   | A7 A B C D E F G
   | A8 A B C D E F G
   | A9 A B C D E F G
   | AA A B C D E F G
   | AB A B C D E F G
   | AC A B C D E F G
   | AD A B C D E F G
   | AE A B C D E F G
   | AF A B C D E F G
data B 
   = B1 A B C D E F G
   | B2 A B C D E F G
   | B3 A B C D E F G
   | B4 A B C D E F G
   | B5 A B C D E F G
   | B6 A B C D E F G
   | B7 A B C D E F G
   | B8 A B C D E F G
   | B9 A B C D E F G
   | BA A B C D E F G
   | BB A B C D E F G
   | BC A B C D E F G
   | BD A B C D E F G
   | BE A B C D E F G
   | BF A B C D E F G
data C
   = C1 A B C D E F G
   | C2 A B C D E F G
   | C3 A B C D E F G
   | C4 A B C D E F G
   | C5 A B C D E F G
   | C6 A B C D E F G
   | C7 A B C D E F G
   | C8 A B C D E F G
   | C9 A B C D E F G
   | CA A B C D E F G
   | CB A B C D E F G
   | CC A B C D E F G
   | CD A B C D E F G
   | CE A B C D E F G
   | CF A B C D E F G
data D
   = D1 A B C D E F G
   | D2 A B C D E F G
   | D3 A B C D E F G
   | D4 A B C D E F G
   | D5 A B C D E F G
   | D6 A B C D E F G
   | D7 A B C D E F G
   | D8 A B C D E F G
   | D9 A B C D E F G
   | DA A B C D E F G
   | DB A B C D E F G
   | DC A B C D E F G
   | DD A B C D E F G
   | DE A B C D E F G
   | DF A B C D E F G
data E
   = E1 A B C D E F G
   | E2 A B C D E F G
   | E3 A B C D E F G
   | E4 A B C D E F G
   | E5 A B C D E F G
   | E6 A B C D E F G
   | E7 A B C D E F G
   | E8 A B C D E F G
   | E9 A B C D E F G
   | EA A B C D E F G
   | EB A B C D E F G
   | EC A B C D E F G
   | ED A B C D E F G
   | EE A B C D E F G
   | EF A B C D E F G

data F
data G
deriveFamily [t| A |]
