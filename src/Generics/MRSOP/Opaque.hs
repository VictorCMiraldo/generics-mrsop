{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE StandaloneDeriving   #-}
-- | A curation of base types commonly used
--   by the everyday Haskell programmer.
module Generics.MRSOP.Opaque where

import Data.Type.Equality
import Generics.MRSOP.Util

-- * Opaque Types
--
-- $opaquetypes
--
-- In order to plug in custom opaque types, the programmer
-- must provide their own 'Kon' and 'Singl'. This module serves
-- more as an example.

-- | Types with kind 'Kon' will be used to
--   index a 'Singl' type with their values inside.
data Kon
  = KInt
  | KInteger
  | KFloat
  | KDouble
  | KBool
  | KChar
  | KString
  deriving (Eq , Show)

-- Vim macro to easily generate: nlywea :: pa -> Singl Kp
-- needs a /S before hand, though.

-- |A singleton GADT for the allowed 'Kon'stants.
data Singl (kon :: Kon) :: * where
  SInt     :: Int     -> Singl 'KInt
  SInteger :: Integer -> Singl 'KInteger
  SFloat   :: Float   -> Singl 'KFloat
  SDouble  :: Double  -> Singl 'KDouble
  SBool    :: Bool    -> Singl 'KBool
  SChar    :: Char    -> Singl 'KChar
  SString  :: String  -> Singl 'KString

deriving instance Eq   (Singl k)

instance Show (Singl k) where
 show (SInt      a) = show a 
 show (SInteger  a) = show a
 show (SFloat    a) = show a
 show (SDouble   a) = show a
 show (SBool     a) = show a
 show (SChar     a) = show a
 show (SString   a) = show a

instance EqHO Singl where
  eqHO = (==)

instance ShowHO Singl where
  showHO = show

-- |Equality over singletons
eqSingl :: Singl k -> Singl k -> Bool
eqSingl = (==)

instance TestEquality Singl where
  testEquality (SInt _) (SInt _)         = Just Refl
  testEquality (SInteger _) (SInteger _) = Just Refl
  testEquality (SFloat _) (SFloat _)     = Just Refl
  testEquality (SDouble _) (SDouble _)   = Just Refl
  testEquality (SBool _) (SBool _)       = Just Refl
  testEquality (SChar _) (SChar _)       = Just Refl
  testEquality (SString _) (SString _)   = Just Refl
  testEquality _ _                       = Nothing
  
