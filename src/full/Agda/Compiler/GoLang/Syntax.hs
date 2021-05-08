
module Agda.Compiler.GoLang.Syntax where

import Data.Map (Map)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Semigroup ( Semigroup )

import Data.Text (Text)

import Agda.Syntax.Common ( Nat )

import Agda.Utils.List1 ( List1, pattern (:|), (<|) )
import qualified Agda.Utils.List1 as List1

-- An untyped lambda calculus with records,
-- and a special self-binder for recursive declarations

data Name = 
  Ident String |
  Symbol String
  deriving (Show, Eq)

data GoTerm = Self 
         | Local LocalId 
         | Global GlobalId 
         | GoVar Nat 
         | GoSwitch GoTerm [GoCase] 
         | GoMethodCall MemberId [GoMethodCallParam] 
         | GoCreateStruct MemberId [GoTerm] 
         | GoIf GoTerm GoTerm GoTerm 
         | GoLet String GoTerm GoTerm 
         | PrimOp GoTerm GoTerm GoTerm 
         | ReturnExpression GoTerm TypeId 
         | Integer Integer 
         | Const String
         | UndefinedTerm
         | GoErased
         | Null
  deriving (Show, Eq)

data GoCase = GoCase MemberId Nat Nat Nat [GoTerm]
  deriving (Show, Eq)

data GoMethodCallParam = GoMethodCallParam GoTerm TypeId
  deriving (Show, Eq)

data GoDef = GoStruct MemberId [TypeId] 
           | GoFunction [GoFunctionSignature] GoTerm 
           | GoInterface MemberId 
  deriving (Show, Eq)

-- Local identifiers are named by De Bruijn indices.
-- Global identifiers are named by string lists.
-- Object members are named by strings.

newtype LocalId = LocalId Nat
  deriving (Eq, Ord, Show)

data TypeId = 
  TypeId String
  | ConstructorType String String
  | GenericFunctionType String String
  | FunctionType String String
  | FunctionReturnElement String
  | EmptyFunctionParameter
  | EmptyType
  | PiType TypeId TypeId
  deriving (Eq, Ord, Show)  


data GoFunctionSignature = 
  OuterSignature MemberId [String] TypeId [TypeId] TypeId |
  -- name, parameter, return parameters (func...), final return type.
  InnerSignature TypeId [TypeId] TypeId
-- parameter, return parameters (func...), final return type.
  deriving (Eq, Ord, Show)  

newtype GlobalId = GlobalId [String]
  deriving (Eq, Ord, Show)

data MemberId
    = MemberId String
    | MemberIndex Int Comment
  deriving (Eq, Ord, Show)

data GoImports
    = GoImportDeclarations [String]
    | GoImportField
    | GoImportUsage String
  deriving (Eq, Ord, Show)

newtype Comment = Comment String
  deriving (Show, Semigroup, Monoid)

instance Eq Comment where _ == _ = True
instance Ord Comment where compare _ _ = EQ


type GoQName = List1 MemberId

data Module = Module
  { modName  :: GlobalId
  , imports  :: [GoImports]
  , exports  :: [GoDef]
  }
  deriving Show