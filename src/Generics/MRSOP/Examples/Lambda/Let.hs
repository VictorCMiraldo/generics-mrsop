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

import Generics.MRSOP.Base
import Generics.MRSOP.Opaque
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
alphaEq = (galphaEq SZ) `on` (deep @FamTermString)
  where
    galphaEq :: forall iy . (IsNat iy)
             => SNat iy
             -> Fix Singl CodesTermString iy
             -> Fix Singl CodesTermString iy
             -> Bool
    galphaEq iy (Fix x) (Fix y)
      = case zipRep x y of
          Nothing -> False
          Just xy -> case iy of
                       SZ      -> case sop xy of
                         Tag cx px -> _
                       (SS SZ) -> _
