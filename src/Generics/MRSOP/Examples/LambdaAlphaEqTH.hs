{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# OPTIONS_HADDOCK hide, prune, ignore-exports #-}
{-# OPTIONS_GHC -Wno-missing-pattern-synonym-signatures #-}
{-# OPTIONS_GHC -Wno-missing-signatures                 #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns                #-}
{-# OPTIONS_GHC -Wno-orphans                            #-}
-- This is the minimun language extensions we
-- need for using the library.
-- |Provide a generic alpha equality decider for the lambda calculus.
module Generics.MRSOP.Examples.LambdaAlphaEqTH where

import Control.Monad.State

import Generics.MRSOP.Util
import Generics.MRSOP.Base
import Generics.MRSOP.Opaque
import Generics.MRSOP.TH

-- |Standard Lambda Calculus.
data Term = Var String
          | Abs String Term
          | App Term Term

deriveFamily [t| Term |]

-- * The alpha-eq monad
--
-- $alphaeqmonad
--
-- We will use an abstract monad for keeping track of scopes and name equivalences
--

-- |Interface needed for deciding alpha equivalence.
class Monad m => MonadAlphaEq m where
  -- |Runs a computation under a new scope.
  onNewScope   :: m a -> m a

  -- |Registers a name equivalence under the current scope.
  addRule      :: String -> String -> m ()
  
  -- |Checks for a name equivalence under all scopes.
  (=~=)        :: String -> String -> m Bool

onHead :: (a -> a) -> [a] -> [a]
onHead f (x : xs) = f x : xs
onHead _ []       = []

-- |Given a list of scopes, which consist in a list of pairs each, checks
--  whether or not two names are equivalent.
onScope :: String -> String -> [[(String , String)]] -> Bool
onScope v1 v2 [] = v1 == v2
onScope v1 v2 (s:ss)
  = case filter (\(x1 , x2) -> x1 == v1 || x2 == v2) s of
      []          -> onScope v1 v2 ss
      [(x1 , x2)] -> x1 == v1 && x2 == v2
      _           -> False

-- |One of the simplest monads that implement 'MonadAlphaEq'
instance MonadAlphaEq (State [[(String, String)]]) where
  onNewScope s
    = modify ([]:) >> s <* modify tail

  addRule v1 v2
    = modify (onHead ((v1 , v2):))

  v1 =~= v2
    = get >>= return . onScope v1 v2

-- |Runs a computation.
runAlpha :: State [[(String , String)]] a -> a
runAlpha = flip evalState [[]]

-- * Alpha equivalence for Lambda terms

type FIX = Fix Singl CodesTerm

-- |Decides whether or not two terms are alpha equivalent.
alphaEq :: Term -> Term -> Bool
alphaEq x y = runAlpha $ galphaEqT (deep @FamTerm x) (deep @FamTerm y)
  where
    galphaEqT :: forall ix m . (MonadAlphaEq m , IsNat ix)
              => FIX ix -> FIX ix
              -> m Bool
    galphaEqT i j = galphaEq (getSNat' @ix) i j

    galphaEq :: forall ix m . (MonadAlphaEq m , IsNat ix)
             => SNat ix -> FIX ix -> FIX ix
             -> m Bool
    galphaEq ix (Fix x0) (Fix y0) = maybe (return False) (go ix) (zipRep x0 y0)

    step :: forall m c . (MonadAlphaEq m)
         => Rep (Singl :*: Singl) (FIX :*: FIX) c -> m Bool
    step = elimRepM (return . uncurry' eqSingl)
                    (uncurry' galphaEqT)
                    (return . and)

    go :: forall ix m . (MonadAlphaEq m)
       => SNat ix -> Rep (Singl :*: Singl) (FIX :*: FIX)
                         (Lkup ix CodesTerm)
       -> m Bool
    go IdxTerm x0 = case sop x0 of
      -- Without -XPolyKinds this is impossible; weird errors all over the place.
      Var_ (SString v1 :*: SString v2)
        -> v1 =~= v2
      Abs_ (SString v1 :*: SString v2) (c1 :*: c2)
        -> onNewScope (addRule v1 v2 >> galphaEq IdxTerm c1 c2)
      _ -> step x0

-- * Tests
--
-- Arguments of type 'String' will be bound
-- by an abstraction, arguments of type 'Char'
-- will be unbound variables.

t1 :: String -> String -> Term
t1 x y = Abs x (Abs y (App (Var x) (Var y)))

t2 :: String -> String -> String -> Char -> Term
t2 a b c d
  = Abs a (App (Abs b (App (Var b) (Var [d]))) (Abs c (App (Var c) (Var [d]))))
