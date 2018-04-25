{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE StandaloneDeriving     #-}
module Generics.MRSOP.Base.Metadata where

import Data.Proxy

import Generics.MRSOP.Util
import Generics.MRSOP.Base.NS
import Generics.MRSOP.Base.NP
import Generics.MRSOP.Base.Universe
import Generics.MRSOP.Base.Class

type ModuleName      = String
type FamilyName      = String
type ConstructorName = String
type FieldName       = String

infixl 5 :@:
data DatatypeName
  = Name String
  | DatatypeName :@: DatatypeName
  deriving (Eq , Show)

data DatatypeInfo :: [[Atom kon]] -> * where
  ADT :: ModuleName -> DatatypeName -> NP ConstructorInfo c
      -> DatatypeInfo c
  New :: ModuleName -> DatatypeName -> ConstructorInfo '[ c ]
      -> DatatypeInfo '[ '[ c ]]

moduleName :: DatatypeInfo code -> ModuleName
moduleName (ADT m _ _) = m
moduleName (New m _ _) = m

datatypeName :: DatatypeInfo code -> DatatypeName
datatypeName (ADT _ d _) = d
datatypeName (New _ d _) = d

constructorInfo :: DatatypeInfo code -> NP ConstructorInfo code
constructorInfo (ADT _ _ c) = c
constructorInfo (New _ _ c) = c :* NP0

data Associativity
  = LeftAssociative
  | RightAssociative
  | NotAssociative
  deriving (Eq , Show)

type Fixity = Int

data ConstructorInfo :: [Atom kon] -> * where
  Constructor :: ConstructorName -> ConstructorInfo xs
  Infix       :: ConstructorName -> Associativity -> Fixity -> ConstructorInfo '[ x , y ]
  Record      :: ConstructorName -> NP FieldInfo xs -> ConstructorInfo xs

constructorName :: ConstructorInfo con -> ConstructorName
constructorName (Constructor c) = c
constructorName (Infix c _ _)   = c
constructorName (Record c _)    = c

data FieldInfo :: Atom kon -> * where
  FieldInfo :: { fieldName :: FieldName } -> FieldInfo k

deriving instance Show (NP ConstructorInfo code)
deriving instance Show (NP FieldInfo code)
deriving instance Show (ConstructorInfo code)
deriving instance Show (DatatypeInfo code)
deriving instance Show (FieldInfo atom)

class (Family ki fam codes) => HasDatatypeInfo ki fam codes ix
    | fam -> codes ki where
  datatypeInfo :: (IsNat ix)
               => Proxy fam -> Proxy ix -> DatatypeInfo (Lkup ix codes)

datatypeInfoFor :: forall ki fam codes ix ty
                 . ( HasDatatypeInfo ki fam codes ix
                   , ix ~ Idx ty fam , Lkup ix fam ~ ty , IsNat ix)
                => Proxy fam -> Proxy ty -> DatatypeInfo (Lkup ix codes)
datatypeInfoFor pf pty = datatypeInfo pf (proxyIdx pf pty)
  where
    proxyIdx :: Proxy fam -> Proxy ty -> Proxy (Idx ty fam)
    proxyIdx _ _ = Proxy

-- ** Utilities for figuring names out

constrInfoLkup :: Constr c sum -> DatatypeInfo sum -> ConstructorInfo (Lkup c sum)
constrInfoLkup c = go c . constructorInfo
  where
    go :: Constr c sum -> NP ConstructorInfo sum -> ConstructorInfo (Lkup c sum)
    go CZ     (ci :* _)   = ci
    go (CS c) (_  :* cis) = go c cis


