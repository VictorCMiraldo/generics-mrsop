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
-- |Uses a more involved example to test some
--  of the functionalities of @generics-mrsop@.
module Generics.MRSOP.Examples.SimpTH where

import Data.Function (on)

import Generics.MRSOP.Base
import Generics.MRSOP.Opaque
import Generics.MRSOP.Util
import Generics.MRSOP.Zipper

import Generics.MRSOP.Examples.LambdaAlphaEqTH hiding (FIX, alphaEq)

import Generics.MRSOP.TH

import Control.Monad
import Control.Monad.State

-- * Simple IMPerative Language:

data Stmt var
  = SAssign var (Exp var)
  | SIf     (Exp var) (Stmt var) (Stmt var)
  | SSeq    (Stmt var) (Stmt var)
  | SReturn (Exp var)
  | SDecl (Decl var)
  | SSkip
  deriving Show

data Decl var
  = DVar var
  | DFun var var (Stmt var)
  deriving Show

data Exp var
  = EVar  var
  | ECall var (Exp var)
  | EAdd (Exp var) (Exp var)
  | ESub (Exp var) (Exp var)
  | ELit Int
  deriving Show

deriveFamily [t| Stmt String |]

pattern Decl_ = SS (SS SZ)
pattern Exp_  = SS SZ
pattern Stmt_ = SZ
-- 
-- pattern SAssign_ v e = Tag CZ (NA_K v :* NA_I e :* NP0)
-- 
-- pattern DVar_ v     = Tag CZ (NA_K v :* NP0)
-- pattern DFun_ f x s = Tag (CS CZ) (NA_K f :* NA_K x :* NA_I s :* NP0)
-- 
-- pattern EVar_ v    = Tag CZ      (NA_K v :* NP0)
-- pattern ECall_ f x = Tag (CS CZ) (NA_K f :* NA_I x :* NP0)

type FIX = Fix Singl CodesStmtString

-- * Alpha Equality Functionality

alphaEqD :: Decl String -> Decl String -> Bool
alphaEqD = (galphaEq Decl_) `on` (deep @FamStmtString)
  where
    -- Generic programming boilerplate;
    -- could be removed. WE are just passing SNat
    -- and Proxies around.
    galphaEq :: forall iy . (IsNat iy)
             => SNat iy -> FIX iy -> FIX iy -> Bool
    galphaEq iy x y = runAlpha (galphaEq' iy x y) 

    galphaEqT :: forall iy m . (MonadAlphaEq m , IsNat iy)
              => FIX iy -> FIX iy -> m Bool
    galphaEqT x y = galphaEq' (getSNat' @iy) x y
    
    galphaEq' :: forall iy m . (MonadAlphaEq m , IsNat iy)
              => SNat iy -> FIX iy -> FIX iy -> m Bool
    galphaEq' iy (Fix x)
      = maybe (return False) (go iy) . zipRep x . unFix

    unSString :: Singl k -> String
    unSString (SString s) = s

    -- Performs one default ste by eliminating the topmost Rep
    -- using galphaEqT on the recursive positions and isEqv
    -- on the atoms.
    step :: forall m c . (MonadAlphaEq m)
         => Rep (Singl :*: Singl) (FIX :*: FIX) c
         -> m Bool
    step = elimRepM (return . uncurry' eqSingl)
                    (uncurry' galphaEqT)
                    (return . and)

    -- The actual important 'patterns'; everything
    -- else is done by 'step'.
    go :: forall iy m . (MonadAlphaEq m)
       => SNat iy
       -> Rep (Singl :*: Singl) (FIX :*: FIX)
              (Lkup iy CodesStmtString)
       -> m Bool
    go Stmt_ x
      = case sop x of
          SAssign_ (SString v1 :*: SString v2) e1e2
            -> addRule v1 v2 >> uncurry' (galphaEq' Exp_) e1e2
          otherwise
            -> step x
    go Decl_ x
      = case sop x of
          DVar_ (SString v1 :*: SString v2)
            -> addRule v1 v2 >> return True
          DFun_ (SString f1 :*: SString f2) (SString x1 :*: SString x2) s
            -> addRule f1 f2 >> onNewScope (addRule x1 x2 >> uncurry' galphaEqT s)
          _ -> step x
    go Exp_ x
      = case sop x of
          EVar_ (SString v1 :*: SString v2)
            -> v1 =~= v2
          ECall_ (SString f1 :*: SString f2) e
            -> (&&) <$> (f1 =~= f2) <*> uncurry' galphaEqT e
          _ -> step x 
    go _ x = step x


{- EXAMPLE

decl fib(n):
  aux = fib(n-1) + fib(n-2);
  return aux;

is alpha eq to

decl fib(x):
  r = fib(x-1) + fib(x-2);
  return r;
-}

test1 :: String -> String -> String -> Decl String
test1 fib n aux = DFun fib n
      $ (SAssign aux (EAdd (ECall fib (ESub (EVar n) (ELit 1)))
                             (ECall fib (ESub (EVar n) (ELit 2)))))
      `SSeq` (SReturn (EVar aux))

test2 :: String -> String -> String -> Decl String
test2 fib n aux = DFun fib n
      $ (SAssign aux (EAdd (ECall fib (ESub (EVar n) (ELit 2)))
                           (ECall fib (ESub (EVar n) (ELit 1)))))
      `SSeq` (SReturn (EVar aux))

{- EXAMPLE

decl f(n):
  decl g(n):
    z = n + 1
    return z
  return g(n)

-}

test3 :: String -> String -> String -> Decl String
test3 n1 n2 z = DFun "f" n1
              $ SDecl (DFun "g" n2
                      $ SAssign z (EAdd (EVar n2) (ELit 1))
                      `SSeq` (SReturn $ EVar z))
         `SSeq` (SReturn $ ECall "g" (EVar n1))


-- ** Zipper test

infixr 4 >>>
(>>>) :: (a -> b) -> (b -> c) -> a -> c
(>>>) = flip (.)

test4 :: Int -> Decl String
test4 n = DFun "test" "n"
        $ (SAssign "x" (EAdd (ELit 10) (ELit n)))
        `SSeq` (SReturn (EVar "x"))
        

test5 :: Maybe (Decl String)
test5 = enter
    >>> down
    >=> down
    >=> down
    >=> down
    >=> right
    >=> update mk42
    >>> leave
    >>> return . unEl
      $ into @FamStmtString (test4 10)
  where
    mk42 :: SNat ix -> El FamStmtString ix -> El FamStmtString ix
    mk42 Exp_ _ = El $ ELit 42
    mk42 _    x = x

