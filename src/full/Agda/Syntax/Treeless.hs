-- GHC 7.4.2 requires this layout for the pragmas. See Issue 1460.
{-# LANGUAGE BangPatterns,
             CPP,
             DeriveDataTypeable,
             DeriveFoldable,
             DeriveFunctor,
             DeriveTraversable,
             FlexibleInstances,
             GeneralizedNewtypeDeriving,
             MultiParamTypeClasses,
             StandaloneDeriving,
             TemplateHaskell #-}

-- | The treeless syntax is intended to be used as input for the compiler backends.
-- It is more low-level than Internal syntax and is not used for type checking.
--
-- Some of the features of treeless syntax are:
-- - case expressions instead of case trees
-- - no instantiated datatypes / constructors
module Agda.Syntax.Treeless
    ( module Agda.Syntax.Abstract.Name
    , module Agda.Syntax.Treeless
    ) where

import Prelude hiding (foldr, mapM, null)

import Data.Map (Map)

-- base-4.7 defines the Num instance for Sum
#if !(MIN_VERSION_base(4,7,0))
import Data.Orphans             ()
#endif

import Data.Typeable (Typeable)

import Agda.Syntax.Literal
import Agda.Syntax.Abstract.Name


type Args = [TTerm]

data TModule
  = TModule
  { mName :: ModuleName
  , mDataRec :: Map QName DataRecDef
  -- ^ Data and record types
  , mFuns :: Map QName FunDef
  }
  deriving (Typeable, Show)

data TType = TType { unEl :: TTerm }
  deriving (Typeable, Show)

data Def a
  = Def
    { name :: QName
    , ty :: TType
    , theDef :: a
    }
  deriving (Typeable, Show)

type DataRecDef = Def DataRecDef'
data DataRecDef'
  = Record
    { drdCon :: ConDef
    }
  | Datatype
    { drdCons :: [ConDef]
    }
  deriving (Typeable, Show)

type ConDef = Def ConDef'
data ConDef'
  = Con
    { cdName :: QName
    }
  deriving (Typeable, Show)

type FunDef = Def FunDef'
data FunDef'
  = Fun
    { fdBody :: TTerm
    }
  | Axiom
  | Primitive
    { fdPrimName :: String
    }
  | ForeignImport
  deriving (Typeable, Show)


-- this currently assumes that TApp is translated in a lazy/cbn fashion.
-- The AST should also support strict translation.
--
-- All local variables are using de Bruijn indices.
data TTerm = TVar Int
           | TDef QName
           | TApp TTerm Args
           | TLam TTerm
           | TLit Literal
           | TCon QName
           | TLet TTerm TTerm
           -- ^ introduces a new local binding. The bound term
           -- MUST only be evaluated if it is used inside the body.
           -- Sharing may happen, but is optional.
           -- It is also perfectly valid to just inline the bound term in the body.
           | TCase TTerm CaseType TTerm [TAlt]
           -- ^ Case scrutinee, case type, default value, alternatives
           | TPi TType TType
           | TUnit -- used for levels right now
           | TSort
           | TErased
           | TError TError
           -- ^ A runtime error, something bad has happened.
  deriving (Typeable, Show)

mkTApp :: TTerm -> Args -> TTerm
mkTApp x [] = x
mkTApp x as = TApp x as

-- | Introduces a new binding
mkLet :: TTerm -> TTerm -> TTerm
mkLet x body = TLet x body


data CaseType
  = CTData QName -- case on datatype
  | CTChar
  | CTString
  deriving (Typeable, Show)

data TAlt
  = TACon    { aCon  :: QName, aArity :: Int, aBody :: TTerm }
  -- ^ Matches on the given constructor. If the match succeeds,
  -- the pattern variables are prepended to the current environment
  -- (pushes all existing variables aArity steps further away)
  | TAChar   { aChar :: Char,   aBody:: TTerm }
  | TAString { aStr  :: String, aBody :: TTerm }
  deriving (Typeable, Show)

data TError
  = TPatternMatchFailure QName -- function name
  deriving (Typeable, Show)
