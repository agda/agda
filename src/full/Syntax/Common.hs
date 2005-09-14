{-| Some common syntactic entities are defined in this module.
-}
module Syntax.Common where

import Syntax.Position

data Name = N Range String

data Hiding = Hidden | NotHidden

type Nat = Int

