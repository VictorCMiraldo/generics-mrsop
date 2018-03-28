-- |
-- Module      : Language.Go.Syntax.AST
-- Copyright   : (c) 2011 Andrew Robbins
-- License     : GPLv3 (see COPYING)
-- 
-- x

{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeApplications        #-}
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
{-# LANGUAGE LambdaCase              #-}
#define GO_AST_DERIVING deriving (Eq, Read, Show)
module Generics.MRSOP.Examples.GoAST where

import Generics.MRSOP.Base
import Generics.MRSOP.Opaque
import Generics.MRSOP.Util
import Generics.MRSOP.TH

-- | Go Language source start
data GoSource = GoSource {
      getPackage      :: GoId,
      getTopLevelPrel :: [GoPrel],
      getTopLevelDecl :: [GoDecl]}
                deriving (Eq, Read, Show)

data GoPrel = GoImportDecl [GoImpSpec]
                deriving (Eq, Read, Show)

data GoDecl = GoConst [GoCVSpec]
            | GoType  [GoTypeSpec]
            | GoVar   [GoCVSpec]
            | GoFunc   GoFuncDecl
            | GoMeth   GoMethDecl
                deriving (Eq, Read, Show)

data GoImpSpec = GoImpSpec GoImpType String
                deriving (Eq, Read, Show)

data GoImpType = GoImp
               | GoImpDot
               | GoImpQual GoId
                deriving (Eq, Read, Show)

data GoCVSpec = GoCVSpec [GoId] (Maybe GoType) [GoExpr]
                deriving (Eq, Read, Show)

data GoTypeSpec  = GoTypeSpec GoId GoType
                deriving (Eq, Read, Show)

data GoFuncExpr  = GoFuncExpr            GoSig GoBlock
                deriving (Eq, Read, Show)

data GoFuncDecl  = GoFuncDecl       GoId GoSig GoBlock
                deriving (Eq, Read, Show)

data GoMethDecl  = GoMethDecl GoRec GoId GoSig GoBlock
                deriving (Eq, Read, Show)

data GoMethSpec  = GoMethSpec  GoId GoSig
                 | GoIfaceName (Maybe GoId) GoId
                deriving (Eq, Read, Show)

-- GoId (= 'identifier')
data GoId = GoId String
                deriving (Eq, Read, Show)

-- GoOp (= 'unary_op' = 'binary_op')
data GoOp = GoOp String
                deriving (Eq, Read, Show)

-- GoRec (= 'Receiver' = 'ReceiverType')
data GoRec = GoRec Bool (Maybe GoId) GoType
                deriving (Eq, Read, Show)

-- GoSig (= 'Signature')
data GoSig = GoSig [GoParam] [GoParam]
                deriving (Eq, Read, Show)

-- GoParam (= 'Parameters')
data GoParam = GoParam [GoId] GoType
                deriving (Eq, Read, Show)

-- GoType (= 'Type' = 'TypeLit' = 'LiteralType')
data GoType = GoTypeName (Maybe GoId) GoId
            | GoArrayType GoExpr GoType
            | GoChannelType GoChanKind GoType
            | GoFunctionType GoSig
            | GoInterfaceType [GoMethSpec]
            | GoMapType GoType GoType
            | GoPointerType GoType
            | GoSliceType GoType
            | GoStructType [GoFieldType]
            | GoEllipsisType GoType  -- only in Literals
            | GoVariadicType GoType  -- only in Funcs
                deriving (Eq, Read, Show)


--data GoChannelKind = GoIChan
--                   | GoOChan
--                   | GoIOChan

data GoChanKind = GoIChan  -- <-chan
                | GoOChan  -- chan<-
                | GoIOChan -- chan
                deriving (Eq, Read, Show)

-- GoFieldType
data GoFieldType = GoFieldType {
      getFieldTag  :: Maybe GoLit,
      getFieldId   :: [GoId],
      getFieldType :: GoType }
                 | GoFieldAnon {
      getFieldTag  :: Maybe GoLit,
      getFieldPtr  :: Bool,
      getFieldType :: GoType } -- MUST be typename
                deriving (Eq, Read, Show)

{-  In the phrases below the symbol / means "is the only production which uses"
In the phrases below the symbol - means "is NOT the only production which uses"
InterfaceType 

PrimaryExpr/Operand
PrimaryExpr/Conversion
PrimaryExpr/BuiltinCall
PrimaryExpr/Selector
PrimaryExpr/Index
PrimaryExpr/Slice
PrimaryExpr/TypeAssertion
PrimaryExpr/Call/ArgumentList

LiteralType - ArrayType
FunctionType - Signature
FunctionDecl - Signature
MethodSpec - Signature
MethodDecl - Signature
-}

-- GoExpr (= 'Expression')
data GoExpr = GoPrim GoPrim           -- 'PrimaryExpr'
            | Go1Op GoOp GoExpr       -- 'Expression/UnaryExpr[2]'
            | Go2Op GoOp GoExpr GoExpr -- 'Expression[2]'
              deriving (Eq, Read, Show)

-- GoPrimExpr (= 'PrimaryExpr')
data GoPrim = GoLiteral GoLit         -- 'PrimaryExpr/Operand/Literal'
            | GoQual (Maybe GoId) GoId -- 'PrimaryExpr/Operand/QualifiedIdent'
            | GoMethod GoRec GoId     -- 'PrimaryExpr/Operand/MethodExpr'
            | GoParen GoExpr          -- 'PrimaryExpr/Operand/MethodExpr'
            | GoCast GoType GoExpr    -- 'PrimaryExpr/Conversion'
            | GoNew  GoType           -- 'PrimaryExpr/BuiltinCall/new'
            | GoMake GoType [GoExpr]  -- 'PrimaryExpr/BuiltinCall/make'
--            | GoBI GoId GoType [GoExpr]  -- 'PrimaryExpr/BuiltinCall'
            | GoSelect GoPrim GoId    -- 'PrimaryExpr/Selector'
            | GoIndex GoPrim GoExpr   -- 'PrimaryExpr/Index'
            | GoSlice GoPrim (Maybe GoExpr) (Maybe GoExpr) -- 'PrimaryExpr/Slice'
            | GoTA    GoPrim GoType   -- 'PrimaryExpr/TypeAssertion'
            | GoCall  GoPrim [GoExpr] Bool -- 'PrimaryExpr/Call'
              deriving (Eq, Read, Show)

-- TODO merge Lit with Prim
-- GoLit (= 'Literal') is only used in one place, operands
data GoLit = GoLitInt  String Integer -- 'Literal/BasicLit/int_lit'
           | GoLitReal String Float   -- 'Literal/BasicLit/float_lit'
           | GoLitImag String Float   -- 'Literal/BasicLit/imaginary_lit'
           | GoLitChar String Char    -- 'Literal/BasicLit/char_lit'
           | GoLitStr  String String  -- 'Literal/BasicLit/string_lit'
           | GoLitComp GoType GoComp  -- 'Literal/CompositeLit'
           | GoLitFunc GoFuncExpr     -- 'Literal/FunctionLit'
             deriving (Eq, Read, Show)

-- GoComp (= 'CompositeLit/LiteralValue') is used in 2 places
data GoComp = GoComp [GoElement]
              deriving (Eq, Read, Show)

data GoElement = GoElement GoKey GoValue
                deriving (Eq, Read, Show)

data GoKey = GoKeyNone
           | GoKeyField GoId
           | GoKeyIndex GoExpr
                deriving (Eq, Read, Show)

data GoValue = GoValueExpr GoExpr -- 'Value/Expression'
             | GoValueComp GoComp -- 'Value/LiteralValue'
                deriving (Eq, Read, Show)

data GoBlock = GoBlock { getStmt::[GoStmt] }
             | GoNoBlock
                deriving (Eq, Read, Show)

data GoForClause = GoForWhile (Maybe GoExpr)
                 | GoForThree GoSimp (Maybe GoExpr) GoSimp
                 | GoForRange [GoExpr] GoExpr Bool -- True if AssignDecl
                deriving (Eq, Read, Show)

data GoStmt = GoStmtDecl GoDecl -- 'Statement/Declaration'
            | GoStmtLabeled GoId GoStmt
            | GoStmtSimple GoSimp
            | GoStmtGo GoExpr
            | GoStmtReturn [GoExpr]
            | GoStmtBreak    (Maybe GoId)
            | GoStmtContinue (Maybe GoId)
            | GoStmtGoto GoId
            | GoStmtFallthrough
            | GoStmtBlock GoBlock
            | GoStmtIf GoCond GoBlock (Maybe GoStmt)
            | GoStmtSelect            [GoCase GoChan]
            | GoStmtSwitch     GoCond [GoCase GoExpr]
            | GoStmtTypeSwitch GoCond [GoCase GoType] (Maybe GoId)
            | GoStmtFor GoForClause GoBlock
            | GoStmtDefer GoExpr
              deriving (Eq, Read, Show)

data GoSimp = GoSimpEmpty
            | GoSimpSend GoExpr GoExpr -- SimpleStmt/SendStmt
            | GoSimpExpr GoExpr        -- SimpleStmt/ExpressionStmt
            | GoSimpInc  GoExpr        -- SimpleStmt/IncDecStmt[1]
            | GoSimpDec  GoExpr        -- SimpleStmt/IncDecStmt[2]
            | GoSimpAsn [GoExpr] GoOp [GoExpr] -- Assignment
            | GoSimpVar [GoId] [GoExpr]      -- ShortVarDecl
              deriving (Eq, Read, Show)

data GoChanR = GoChanR GoExpr (Maybe GoExpr) GoOp
            deriving (Eq, Read, Show)

data GoChan = GoChanRecv (Maybe GoChanR) GoExpr
            | GoChanSend GoExpr GoExpr
              deriving (Eq, Read, Show)

data GoCond = GoCond (Maybe GoSimp) (Maybe GoExpr)
              deriving (Eq, Read, Show)
data GoCase a = GoCase [a] [GoStmt]
              | GoDefault  [GoStmt]
                deriving (Eq, Read, Show)
deriveFamily [t| GoType |]
