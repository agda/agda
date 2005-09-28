{-| Some common syntactic entities are defined in this module.
-}
module Syntax.Common where

import Syntax.Position

data Hiding = Hidden | NotHidden

type Nat = Int

data Literal = LitInt Range Integer
	     | LitString Range String
	     | LitChar Range Char
	     | LitDouble Range Double

