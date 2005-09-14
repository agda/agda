
{-| The concrete syntax is a raw representation of the program text
    without any desugaring at all.  This is what the parser produces.
    The idea is that if we figure out how to keep the concrete syntax
    around, it can be printed exactly as the user wrote it.

    The concrete syntax supports both a sugared and a desugared view.
-}
module Syntax.Concrete
    ( -- * The concrete syntax
      Expr
      -- * The raw view
    , RawExpr(..)
    , rawView
      -- * The desugared view
    )
    where

import Syntax.Position
import Syntax.Common

-- | The concrete syntax representation. Abstract.
newtype Expr = Expr RawExpr

-- | Reveal the raw structure of an expression.
rawView :: Expr -> RawExpr
rawView (Expr e) = e

-- | Unfold the raw view.
unRawView :: RawExpr -> Expr
unRawView = Expr

-- | The raw view. Should represent exactly what the user wrote.
data RawExpr
	    = Name Name				-- ^ . @x@
	    | Lit Literal			-- ^ . @1@ or @"foo"@
	    | QuestionMark Range		-- ^ . @?@ or @{! ... !}@
	    | Underscore Range			-- ^ . @_@
	    | App Hiding Expr Expr		-- ^ . @e e@ or @e {e}@
	    | Lam Range [LamBinding] Expr	-- ^ . @\L -> e@
	    | Fun Hiding Expr Expr		-- ^ . @e -> e@ or @{e} -> e@
	    | Pi TypedBinding Expr		-- ^ . @(xs:e) -> e@ or @{xs:e} -> e@
	    | Set Range | Prop Range		-- ^ . @Set, Prop@
	    | SetN Range Nat			-- ^ . @Set0, Set1, ..@
	    | Let Range [LocalDefinition] Expr	-- ^ . @let Ds in e@

data Literal = LitInt Range Integer
	     | LitString Range String
	     | LitChar Range Char
	     | LitDouble Range Double

data LamBinding
	= DomainFree Hiding Name		-- x or {x}
	| DomainFull TypedBinding		-- (xs:e) or {xs:e}

data TypedBinding
	= TypedBinding Range Hiding [Name] Expr -- (xs:e) or {xs:e}

