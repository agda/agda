{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Agda.Compiler.JS.Syntax where

import Data.Map (Map)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Semigroup ( Semigroup )

import Data.Text (Text)

import Agda.Syntax.Common ( Nat )

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
  Array [(Comment, Exp)] |
  Apply Exp [Exp] |
  Lookup Exp MemberId |
  If Exp Exp Exp |
  BinOp Exp String Exp |
  PreOp String Exp |
  Const String |
  PlainJS String -- ^ Arbitrary JS code.
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

-- The top-level compilation unit is a module, which names
-- the GId of its exports, and a list of definitions

data Export = Export { expName :: [MemberId], defn :: Exp }
  deriving Show

data Module = Module
  { modName :: GlobalId
  , imports :: [GlobalId]
  , exports :: [Export]
  , postscript :: Maybe Exp
  }
  deriving Show

-- Note that modules are allowed to be recursive, via the Self expression,
-- which is bound to the exported module.

-- Top-level uses of the form exports.l1....lN.

class Uses a where
  uses :: a -> Set [MemberId]

  default uses :: (a ~ t b, Foldable t, Uses b) => a -> Set [MemberId]
  uses = foldMap uses

instance Uses a => Uses [a]
instance Uses a => Uses (Map k a)

instance (Uses a, Uses b) => Uses (a, b) where
  uses (a, b) = uses a `Set.union` uses b

instance (Uses a, Uses b, Uses c) => Uses (a, b, c) where
  uses (a, b, c) = uses a `Set.union` uses b `Set.union` uses c

instance Uses Comment where
  uses _ = Set.empty

instance Uses Exp where
  uses (Object o)     = uses o
  uses (Array es)     = uses es
  uses (Apply e es)   = uses (e, es)
  uses (Lookup e l)   = uses' e [l] where
      uses' Self         ls = Set.singleton ls
      uses' (Lookup e l) ls = uses' e (l : ls)
      uses' e            ls = uses e
  uses (If e f g)     = uses (e, f, g)
  uses (BinOp e op f) = uses (e, f)
  uses (PreOp op e)   = uses e
  uses e              = Set.empty

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

instance Globals Comment where
  globals _ = Set.empty

instance Globals Exp where
  globals (Global i) = Set.singleton i
  globals (Lambda n e) = globals e
  globals (Object o) = globals o
  globals (Array es) = globals es
  globals (Apply e es) = globals (e, es)
  globals (Lookup e l) = globals e
  globals (If e f g) = globals (e, f, g)
  globals (BinOp e op f) = globals (e, f)
  globals (PreOp op e) = globals e
  globals _ = Set.empty

instance Globals Export where
  globals (Export _ e) = globals e

instance Globals Module where
  globals (Module _ _ es me) = globals (es, me)
