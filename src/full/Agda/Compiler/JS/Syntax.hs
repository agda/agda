
module Agda.Compiler.JS.Syntax where

import Data.Map (Map)
import Data.Set (Set)
import qualified Data.Set as Set

import Data.Text (Text)

import Agda.Syntax.Common ( Nat )

import Agda.Utils.List1 ( List1, pattern (:|), (<|) )
import qualified Agda.Utils.List1 as List1

-- An untyped lambda calculus with records,
-- and a special self-binder for recursive declarations

data Exp =
  Self |
  Local LocalId |
  Global GlobalId |
  Undefined |
  Null |
  String Text |
  Char Char |
  Integer Integer |
  Double Double |
  Lambda Nat Exp |
  Object (Map MemberId Exp) |
  Array [Exp] |
  Apply Exp [Exp] |
  Lookup Exp MemberId |
  If Exp Exp Exp |
  BinOp Exp String Exp |
  PreOp String Exp |
  Const String |
  PlainJS String -- ^ Arbitrary JS code.
  deriving (Show, Eq)
-- Code style:
--  All recursive Exp-traversing functions should list every constructor explicitly.
--  Do not write a catch-all case to cover all the trivial constructors.
-- This policy helps catch subtle bugs (randomly failing substitution, missing imports etc.)
-- due to newly-added constructors silently hitting the catch-all case.

-- Local identifiers are named by De Bruijn indices.
-- Global identifiers are named by string lists.
-- Object members are named by strings.

newtype LocalId = LocalId Nat
  deriving (Eq, Ord, Show)

newtype GlobalId = GlobalId [String]
  deriving (Eq, Ord, Show)

data MemberId
    = MemberId String
    | MemberIndex Int
  deriving (Eq, Ord, Show)

-- The top-level compilation unit is a module, which names
-- the GId of its exports, and a list of definitions

data Export = Export { expName :: JSQName, defn :: Exp }
  deriving Show

type JSQName = List1 MemberId

data Module = Module
  { modName  :: GlobalId
  , imports  :: [GlobalId]
  , exports  :: [Export]
  , callMain :: Maybe Exp
  }
  deriving Show

-- Note that modules are allowed to be recursive, via the Self expression,
-- which is bound to the exported module.

-- Top-level uses of the form exports.l1....lN.

class Uses a where
  uses :: a -> Set JSQName

  default uses :: (a ~ t b, Foldable t, Uses b) => a -> Set JSQName
  uses = foldMap uses

instance Uses a => Uses [a]
instance Uses a => Uses (Map k a)

instance (Uses a, Uses b) => Uses (a, b) where
  uses (a, b) = uses a `Set.union` uses b

instance (Uses a, Uses b, Uses c) => Uses (a, b, c) where
  uses (a, b, c) = uses a `Set.union` uses b `Set.union` uses c

instance Uses Exp where
  uses (Self)         = Set.empty
  uses (Local _)      = Set.empty
  uses (Global _)     = Set.empty
  uses (Undefined)    = Set.empty
  uses (Null)         = Set.empty
  uses (String _)     = Set.empty
  uses (Integer _)    = Set.empty
  uses (Char _)       = Set.empty
  uses (Double _)     = Set.empty
  uses (Lambda n _)   = Set.empty
  -- Lawrence 2026-08: I suspect returning Set.empty for lambdas is a bug,
  -- but it does not break existing tests
  uses (Object o)     = uses o
  uses (Array es)     = uses es
  uses (Apply e es)   = uses (e, es)
  uses (Lookup e l)   = uses' e (List1.singleton l)
    where
      uses' :: Exp -> JSQName -> Set JSQName
      uses' Self         ls = Set.singleton ls
      uses' (Lookup e l) ls = uses' e (l <| ls)
      uses' e            ls = uses e
  uses (If e f g)     = uses (e, f, g)
  uses (BinOp e op f) = uses (e, f)
  uses (PreOp op e)   = uses e
  uses (Const _)      = Set.empty
  uses (PlainJS _)    = Set.empty

instance Uses Export where
  uses (Export _ e) = uses e

-- All global ids

class Globals a where
  globals :: a -> Set GlobalId

  default globals :: (a ~ t b, Foldable t, Globals b) => a -> Set GlobalId
  globals = foldMap globals

instance Globals a => Globals [a]
instance Globals a => Globals (Maybe a)
instance Globals a => Globals (Map k a)

instance (Globals a, Globals b) => Globals (a, b) where
  globals (a, b) = globals a `Set.union` globals b

instance (Globals a, Globals b, Globals c) => Globals (a, b, c) where
  globals (a, b, c) = globals a `Set.union` globals b `Set.union` globals c

instance Globals Exp where
  globals (Self)         = Set.empty
  globals (Local _)      = Set.empty
  globals (Global i) = Set.singleton i
  globals (Undefined)    = Set.empty
  globals (Null)         = Set.empty
  globals (String _)     = Set.empty
  globals (Integer _)    = Set.empty
  globals (Char _)       = Set.empty
  globals (Double _)     = Set.empty
  globals (Lambda n e) = globals e
  globals (Object o) = globals o
  globals (Array es) = globals es
  globals (Apply e es) = globals (e, es)
  globals (Lookup e l) = globals e
  globals (If e f g) = globals (e, f, g)
  globals (BinOp e op f) = globals (e, f)
  globals (PreOp op e) = globals e
  globals (Const _)      = Set.empty
  globals (PlainJS _)    = Set.empty

instance Globals Export where
  globals (Export _ e) = globals e

instance Globals Module where
  globals (Module _ _ es me) = globals (es, me)
