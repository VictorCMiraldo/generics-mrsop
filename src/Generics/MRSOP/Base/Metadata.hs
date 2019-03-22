{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE StandaloneDeriving     #-}
-- |Metadata maintenance; usefull for pretty-printing values.
module Generics.MRSOP.Base.Metadata where

import Data.Proxy

import Generics.MRSOP.Util
import Generics.MRSOP.Base.NP
import Generics.MRSOP.Base.Universe
import Generics.MRSOP.Base.Class

type ModuleName      = String
type FamilyName      = String
type ConstructorName = String
type FieldName       = String

-- |Since we only handled fully saturated datatypes, a 'DatatypeName'
--  needs to remember what were the arguments applied to a type.
--
--  The type @[Int]@ is represented by @Name "[]" :@@: Name "Int"@
--
infixl 5 :@:
data DatatypeName
  = Name String
  | DatatypeName :@: DatatypeName
  deriving (Eq , Show)

-- |Provides information about the declaration of a datatype.
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

-- |Associativity information for infix constructors.
data Associativity
  = LeftAssociative
  | RightAssociative
  | NotAssociative
  deriving (Eq , Show)

-- |Fixity information for infix constructors.
type Fixity = Int

-- |Constructor metadata.
data ConstructorInfo :: [Atom kon] -> * where
  Constructor :: ConstructorName -> ConstructorInfo xs
  Infix       :: ConstructorName -> Associativity -> Fixity -> ConstructorInfo '[ x , y ]
  Record      :: ConstructorName -> NP FieldInfo xs -> ConstructorInfo xs

constructorName :: ConstructorInfo con -> ConstructorName
constructorName (Constructor c) = c
constructorName (Infix c _ _)   = c
constructorName (Record c _)    = c

-- |Record fields metadata
data FieldInfo :: Atom kon -> * where
  FieldInfo :: { fieldName :: FieldName } -> FieldInfo k

deriving instance Show (FieldInfo atom)

instance ShowHO FieldInfo where
  showHO = show

deriving instance Show (ConstructorInfo code)

instance ShowHO ConstructorInfo where
  showHO = show

deriving instance Show (DatatypeInfo code)

-- |Given a 'Family', provides the 'DatatypeInfo' for the type
--  with index @ix@ in family 'fam'.
class (Family ki fam codes) => HasDatatypeInfo ki fam codes
    | fam -> codes ki where
  datatypeInfo :: Proxy fam -> SNat ix -> DatatypeInfo (Lkup ix codes)

-- |Sometimes it is more convenient to use a proxy of the type
--  in the family instead of indexes.
datatypeInfoFor :: forall ki fam codes ix ty
                 . ( HasDatatypeInfo ki fam codes
                   , ix ~ Idx ty fam , Lkup ix fam ~ ty , IsNat ix)
                => Proxy fam -> Proxy ty -> DatatypeInfo (Lkup ix codes)
datatypeInfoFor pf pty = datatypeInfo pf (getSNat $ proxyIdx pf pty)
  where
    proxyIdx :: Proxy fam -> Proxy ty -> Proxy (Idx ty fam)
    proxyIdx _ _ = Proxy

-- ** Name Lookup

-- |This is essentially a list lookup, but needs significant type
--  information to go through. Returns the name of the @c@th constructor
--  of a sum-type.
constrInfoLkup :: Constr sum c -> DatatypeInfo sum -> ConstructorInfo (Lkup c sum)
constrInfoLkup c = go c . constructorInfo
  where
    go :: Constr sum c -> NP ConstructorInfo sum -> ConstructorInfo (Lkup c sum)
    go CZ      (ci :* _)   = ci
    go (CS c0) (_  :* cis) = go c0 cis


-- |Returns the constructor information for a given
--  type in the family.
constrInfoFor :: (HasDatatypeInfo ki fam codes)
              => Proxy fam
              -> SNat ix
              -> Constr (Lkup ix codes) c
              -> ConstructorInfo (Lkup c (Lkup ix codes))
constrInfoFor pfam six c = constrInfoLkup c (datatypeInfo pfam six)
               

