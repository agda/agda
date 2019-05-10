
module Agda.Compiler.JS.Syntax where

import Data.Map ( Map )
import qualified Data.Map as Map

import Data.Set ( Set, empty, singleton, union )

import Agda.Syntax.Common ( Nat )

-- An untyped lambda calculus with records,
-- and a special self-binder for recursive declarations

data Exp =
  Self |
  Local LocalId |
  Global GlobalId |
  Undefined |
  String String |
  Char Char |
  Integer Integer |
  Double Double |
  Lambda Nat Exp |
  Object (Map MemberId Exp) |
  Apply Exp [Exp] |
  Lookup Exp MemberId |
  If Exp Exp Exp |
  BinOp Exp String Exp |
  PreOp String Exp |
  Const String |
  PlainJS String -- ^ Arbitrary JS code.
  deriving Show

-- Local identifiers are named by De Bruijn indices.
-- Global identifiers are named by string lists.
-- Object members are named by strings.

newtype LocalId = LocalId Nat
  deriving (Eq, Ord, Show)

newtype GlobalId = GlobalId [String]
  deriving (Eq, Ord, Show)

newtype MemberId = MemberId String
  deriving (Eq, Ord, Show)

-- The top-level compilation unit is a module, which names
-- the GId of its exports, and a list of definitions

data Export = Export { expName :: [MemberId], defn :: Exp }
  deriving Show

data Module = Module { modName :: GlobalId, exports :: [Export], postscript :: Maybe Exp }
  deriving Show

-- Note that modules are allowed to be recursive, via the Self expression,
-- which is bound to the exported module.

-- Top-level uses of the form exports.l1....lN.

class Uses a where
  uses :: a -> Set [MemberId]

instance Uses a => Uses [a] where
  uses = foldr (union . uses) empty

instance Uses a => Uses (Map k a) where
  uses = Map.foldr (union . uses) empty

instance Uses Exp where
  uses (Object o)     = Map.foldr (union . uses) empty o
  uses (Apply e es)   = foldr (union . uses) (uses e) es
  uses (Lookup e l)   = uses' e [l] where
      uses' Self         ls = singleton ls
      uses' (Lookup e l) ls = uses' e (l : ls)
      uses' e            ls = uses e
  uses (If e f g)     = uses e `union` uses f `union` uses g
  uses (BinOp e op f) = uses e `union` uses f
  uses (PreOp op e)   = uses e
  uses e              = empty

instance Uses Export where
  uses (Export _ e) = uses e

-- All global ids

class Globals a where
  globals :: a -> Set GlobalId

instance Globals a => Globals [a] where
  globals = foldr (union . globals) empty

instance Globals a => Globals (Map k a) where
  globals = Map.foldr (union . globals) empty

instance Globals Exp where
  globals (Global i) = singleton i
  globals (Lambda n e) = globals e
  globals (Object o) = globals o
  globals (Apply e es) = globals e `union` globals es
  globals (Lookup e l) = globals e
  globals (If e f g) = globals e `union` globals f `union` globals g
  globals (BinOp e op f) = globals e `union` globals f
  globals (PreOp op e) = globals e
  globals _ = empty

instance Globals Export where
  globals (Export _ e) = globals e

instance Globals Module where
  globals (Module m es _) = globals es
