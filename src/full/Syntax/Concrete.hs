
{-| The concrete syntax is a raw representation of the program text
    without any desugaring at all.  This is what the parser produces.
    The idea is that if we figure out how to keep the concrete syntax
    around, it can be printed exactly as the user wrote it.

    The concrete syntax supports both a sugared and a desugared view.
-}
module Syntax.Concrete
    ( -- * The concrete syntax
      Expr
      -- * The sugared view
      -- * The desugared view
    )
    where

import Syntax.Position

-- | The concrete syntax representation. Abstract.
data Expr   = Name String

