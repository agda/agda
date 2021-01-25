
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

data Exp =
  Self |
  Local LocalId |
  Global GlobalId |
  Undefined |
  Null |
  GoInterface MemberId |
  GoStruct MemberId [Exp] |
  ConField LocalId String |
  String Text |
  Char Char |
  Integer Integer |
  Const String
  deriving (Show, Eq)

-- Local identifiers are named by De Bruijn indices.
-- Global identifiers are named by string lists.
-- Object members are named by strings.

newtype LocalId = LocalId Nat
  deriving (Eq, Ord, Show)

newtype GlobalId = GlobalId [String]
  deriving (Eq, Ord, Show)

data MemberId
    = MemberId String
    | MemberIndex Int Comment
  deriving (Eq, Ord, Show)

newtype Comment = Comment String
  deriving (Show, Semigroup, Monoid)

instance Eq Comment where _ == _ = True
instance Ord Comment where compare _ _ = EQ


type GoQName = List1 MemberId

data Module = Module
  { modName  :: GlobalId
  , imports  :: [GlobalId]
  , exports  :: [Exp]
  }
  deriving Show