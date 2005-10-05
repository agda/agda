{-| Some common syntactic entities are defined in this module.
-}
module Syntax.Common where

import Syntax.Position

data Hiding  = Hidden | NotHidden

-- | Functions can be defined in both infix and prefix style. See
--   'Syntax.Concrete.LHS'.
data IsInfix = InfixDef | PrefixDef

data Name = Name Range String
    deriving (Eq, Show)

-- | A name can be qualified by a name space. Name spaces are hierarchical
--   so we use a list of strings to represent them.
data QName = QName [String] Name
    deriving (Eq, Show)

type Nat = Int

data Literal = LitInt Range Integer
	     | LitFloat Range Double
	     | LitString Range String
	     | LitChar Range Char
    deriving (Eq, Show)

instance HasRange Name where
    getRange (Name r _)	    = r

instance HasRange QName where
    getRange (QName _ x)    = getRange x

instance HasRange Literal where
    getRange (LitInt r _)	= r
    getRange (LitFloat r _)	= r
    getRange (LitString r _)	= r
    getRange (LitChar r _)	= r

