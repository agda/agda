{-| Some common syntactic entities are defined in this module.
-}
module Syntax.Common where

import Syntax.Position

data Hiding = Hidden | NotHidden

data Name = Name Range String
    deriving (Eq, Show)

type Nat = Int

data Literal = LitInt Range Integer
	     | LitString Range String
	     | LitChar Range Char
	     | LitDouble Range Double

