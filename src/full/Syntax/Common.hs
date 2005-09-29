{-| Some common syntactic entities are defined in this module.
-}
module Syntax.Common where

import Syntax.Position

data Hiding = Hidden | NotHidden

data Name = Name Range String
    deriving (Eq, Show)

-- | A name can be qualified by a name space. Name spaces are hierarchical
--   so we use a list of strings to represent them.
data QName = QName [String] Name
    deriving (Eq, Show)

type Nat = Int

data Literal = LitInt Range Integer
	     | LitString Range String
	     | LitChar Range Char
	     | LitFloat Range Double
    deriving (Eq, Show)

