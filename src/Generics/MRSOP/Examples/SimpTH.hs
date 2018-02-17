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
{-# LANGUAGE PatternSynonyms         #-}
module Generics.MRSOP.Examples.SimpTH where

import Data.Function (on)

import Generics.MRSOP.Base
import Generics.MRSOP.Opaque
import Generics.MRSOP.Util

import Generics.MRSOP.TH

import Control.Monad

-- * Simple IMPerative Language:

data Stmt var
  = SAssign var (Exp var)
  | SIf     (Exp var) (Stmt var) (Stmt var)
  | SSeq    (Stmt var) (Stmt var)
  | SReturn (Exp var)
  | SDecl (Decl var)
  | SSkip

data Decl var
  = DVar var
  | DFun String [var] (Stmt var)

data Exp var
  = EVar  var
  | ECall String [Exp var]

{- EXAMPLE

decl fib(n):
  aux = fib(n-1) + fib(n-2);
  return aux;

is alpha eq to

decl fib(x):
  r = fib(x-1) + fib(x-2);
  return r;
-}

deriveFamily [t| Stmt String |]

pattern Decl_ = SS (SS SZ)
pattern Exp_  = SS SZ
pattern Stmt_ = SZ

pattern SAssign_ v e = Tag CZ (NA_K v :* NA_I e :* NP0)
pattern EVar_    = CS CZ

type FIX = Fix Singl CodesStmtString

alphaEq :: Decl String -> Decl String -> Bool
alphaEq = (galphaEq [] Decl_) `on` (deep @FamStmtString)
  where
    galphaEq :: forall iy . (IsNat iy)
             => [[(String,String)]]
             -> SNat iy -> FIX iy -> FIX iy -> Bool
    galphaEq eqs iy (Fix x)
      = maybe False (go eqs iy) . zipRep x . unFix

    addvar :: String -> String
            -> [[ (String , String) ]]
            -> [[ (String , String) ]]
    addvar v1 v2 (x:xs) = ((v1 , v2):x):xs

    isvalid :: [[ (String , String) ]]
            -> Singl k -> Singl k -> Bool
    isvalid eqs (SString v) (SString k) = _

    go :: forall iy
        . [[ (String , String) ]]
       -> SNat iy
       -> Rep (Singl :*: Singl) (FIX :*: FIX)
              (Lkup iy CodesStmtString)
       -> Bool
    go eqs Stmt_ x
      = case sop x of
          SAssign_ (SString v1 :*: SString v2) e1e2
            -> uncurry' (galphaEq (addvar v1 v2 eqs) Exp_) e1e2 
          otherwise
            -> _
