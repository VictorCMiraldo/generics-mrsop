{-# LANGUAGE TypeApplications        #-}
{-# LANGUAGE RankNTypes              #-}
{-# LANGUAGE FlexibleContexts        #-}
{-# LANGUAGE FlexibleInstances       #-}
{-# LANGUAGE GADTs                   #-}
{-# LANGUAGE TypeOperators           #-}
{-# LANGUAGE DataKinds               #-}
{-# LANGUAGE PolyKinds               #-}
{-# LANGUAGE ScopedTypeVariables     #-}
{-# LANGUAGE FunctionalDependencies  #-}
{-# LANGUAGE TemplateHaskell         #-}
{-# LANGUAGE LambdaCase              #-}
module Generics.MRSOP.Examples.Lambda.Let where

import Data.Function (on)

import Generics.MRSOP.Base.Internal.NS
import Generics.MRSOP.Base.Internal.NP
import Generics.MRSOP.Base.Universe
import Generics.MRSOP.Base.Class
import Generics.MRSOP.Konstants
import Generics.MRSOP.Util

import Generics.MRSOP.TH

import Control.Monad

-- * Lambda Terms:

data Term var
  = Var var
  | Let [Binding var]
  | App (Term var) (Term var)
  | Abs var (Term var)
  deriving (Eq , Show)

data Binding var
  = Bind var (Term var)
  deriving (Eq , Show)

deriveFamily [t| Term String |]

alphaEq :: Term String -> Term String -> Bool
alphaEq t1 t2 = galphaEq (from' @Singl t1) (from t2)
  where
    galphaEq :: FAM ix -> FAM ix -> Bool
    galphaEq (Fix (Rep t)) (Fix (Rep u))
      = undefined
