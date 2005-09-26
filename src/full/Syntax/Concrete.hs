{-# OPTIONS -fglasgow-exts -cpp #-}

{-| The concrete syntax is a raw representation of the program text
    without any desugaring at all.  This is what the parser produces.
    The idea is that if we figure out how to keep the concrete syntax
    around, it can be printed exactly as the user wrote it.

    The concrete syntax supports both a sugared and a desugared view.
-}
module Syntax.Concrete
    ( -- * The concrete syntax
      Expr
    , Definitions
    , LocalDefinitions
    , TypeSignature
    , Constructor
    , Branch(..)
    , LamBinding(..)
    , TypedBinding(..)
    , Telescope
    , LHS, RHS, WhereClause
      -- * The raw view
      -- ** Expressions
    , RawExpr(..)
    , rawExpr
    , unRawExpr
      -- ** Definitions
    , RawDefinition
    , RawLocalDefinition
    , RawTypeSignature
    , RawDefinitionI(..)
    , Local, TopLevel, MaybeTypeSig, OnlyTypeSig
    , rawLocalDef
    , unRawLocalDef
    , rawDef
    , unRawDef
    , rawTypeSig
    , unRawTypeSig
      -- * The desugared view
    )
    where

import Syntax.Position
import Syntax.Common

-- | The concrete syntax representation. Abstract.
newtype Expr = Expr RawExpr

-- | Reveal the raw structure of an expression.
rawExpr :: Expr -> RawExpr
rawExpr (Expr e) = e

-- | Unfold the raw view.
unRawExpr :: RawExpr -> Expr
unRawExpr = Expr

-- | Local definitions are the definitions that can appear in a let.
--   Everything but modules and postulates.
newtype LocalDefinitions = LocalDefs [RawLocalDefinition]

-- | Reveal the raw structure of a block of local definitions.
rawLocalDef :: LocalDefinitions -> [RawLocalDefinition]
rawLocalDef (LocalDefs ds) = ds

-- | Unfold the raw view of a block of local definitions.
unRawLocalDef :: [RawLocalDefinition] -> LocalDefinitions
unRawLocalDef = LocalDefs

-- | Top level definitions include local definitions plus modules and
--   postulates.
newtype Definitions = Defs [RawDefinition]

-- | Reveal the raw structure of a block of top level definitions.
rawDef :: Definitions -> [RawDefinition]
rawDef (Defs ds) = ds

-- | Unfold the raw view of a block of top level definitions.
unRawDef :: [RawDefinition] -> Definitions
unRawDef = Defs

-- | A type signature is a special kind of definition.
--   Occurs in 'Postulate's and 'Data' constructor definitions.
newtype TypeSignature = TypeSignature RawTypeSignature

-- | A constructor declaration is just a type signature.
type Constructor = TypeSignature

-- | Reveal the raw structure of a type signature.
rawTypeSig :: TypeSignature -> RawTypeSignature
rawTypeSig (TypeSignature ds) = ds

-- | Unfold the raw view of type signature.
unRawTypeSig :: RawTypeSignature -> TypeSignature
unRawTypeSig = TypeSignature

-- | The raw view. Should represent exactly what the user wrote.
data RawExpr
	    = Name Name				    -- ^ . @x@
	    | Lit Literal			    -- ^ . @1@ or @\"foo\"@
	    | QuestionMark Range		    -- ^ . @?@ or @{! ... !}@
	    | Underscore Range			    -- ^ . @_@
	    | App Hiding Expr Expr		    -- ^ . @e e@ or @e {e}@
	    | InfixApp Expr Name Expr		    -- ^ . @e + e@ (no hiding)
	    | Lam Range [LamBinding] Expr	    -- ^ . @\L -> e@
	    | Fun Hiding Expr Expr		    -- ^ . @e -> e@ or @{e} -> e@
	    | Pi TypedBinding Expr		    -- ^ . @(xs:e) -> e@ or @{xs:e} -> e@
	    | Set Range | Prop Range		    -- ^ . @Set, Prop@
	    | SetN Range Nat			    -- ^ . @Set0, Set1, ..@
	    | Let Range LocalDefinitions Expr	    -- ^ . @let Ds in e@
	    | Elim Range Expr (Maybe Expr) [Branch] -- ^ . @by e with P of bs@

-- | A (fancy) case branch is on the form @p1 .. pn -> e@ where @pi@ are arbitrary
--   expressions.
data Branch = Branch [Expr] Expr

-- | A lambda binding is either domain free or typed.
data LamBinding
	= DomainFree Hiding Name		-- ^ . @x@ or @{x}@
	| DomainFull TypedBinding		-- ^ . @(xs:e)@ or @{xs:e}@

-- | A typed binding. Appears in dependent function spaces, typed lambdas, and
--   telescopes.
data TypedBinding
	= TypedBinding Range Hiding [Name] Expr -- (xs:e) or {xs:e}

-- | A telescope is a sequence of typed bindings. Bound variables are in scope
--   in later types.
type Telescope = [TypedBinding]

-- | To be able to parse infix definitions properly left hand sides are parsed
--   as expressions. For instance, @x::xs ++ ys = x :: (xs ++ ys)@ should be a
--   valid definition of @++@ provided @::@ has higher precedence than @++@.
type LHS = Expr

type RHS	    = Expr
type WhereClause    = LocalDefinitions

{--------------------------------------------------------------------------
    The raw view
 --------------------------------------------------------------------------}

data Local
data TopLevel
data OnlyTypeSig
data MaybeTypeSig

type RawLocalDefinition = RawDefinitionI MaybeTypeSig Local
type RawTypeSignature	= RawDefinitionI OnlyTypeSig Local
type RawDefinition	= RawDefinitionI MaybeTypeSig TopLevel

{-| RawDefinitionI is family of datatypes indexed by the datakinds

    @
    datakind TypeSig = 'OnlyTypeSig' | 'MaybeTypeSig'
    datakind Local   = 'Local' | 'TopLevel'
    @

    In the raw view of a definition there is no grouping of function clauses
    and\/or type signatures.
#if __GLASGOW_HASKELL__ < 604 || __HADDOCK__
#if __GLASGOW_HASKELL__ < 604
    Without inductive families (introduced in ghc 6.4) the type checker
    cannot help us out here.
#else
    Unfortunately Haddock doesn't support inductive families (yet), but in the
    source code it is an inductive familily.
#endif
    The intended targets of the constructors are in the comments.
-}
data RawDefinitionI typesig local
	= TypeSig Name Expr				-- ^ . @RawDefinitionI typesig local@
	| FunClause LHS RHS WhereClause			-- ^ . @RawDefinitionI 'MaybeTypeSig' local@
	| Data Range Name Telescope Expr [Constructor]	-- ^ . @RawDefinitionI 'MaybeTypeSig' local@
	| Mutual Range Definitions			-- ^ . @RawDefinitionI 'MaybeTypeSig' local@
	| Abstract Range Definitions			-- ^ . @RawDefinitionI 'MaybeTypeSig' local@
	| Private Range Definitions			-- ^ . @RawDefinitionI 'MaybeTypeSig' 'TopLevel'@
	| Postulate Range [TypeSignature]		-- ^ . @RawDefinitionI 'MaybeTypeSig' 'TopLevel'@
	| Module Range Name Telescope Definitions	-- ^ . @RawDefinitionI 'MaybeTypeSig' 'TopLevel'@

#else
-}
data RawDefinitionI typesig local where
	TypeSig	    :: Name -> Expr		-> RawDefinitionI typesig local
	FunClause   :: LHS -> RHS -> WhereClause
						-> RawDefinitionI MaybeTypeSig local
	Data	    :: Range -> Name -> Telescope -> Expr -> [Constructor] 
						-> RawDefinitionI MaybeTypeSig local
	Mutual	    :: Range -> Definitions	-> RawDefinitionI MaybeTypeSig local
	Abstract    :: Range -> Definitions	-> RawDefinitionI MaybeTypeSig local
	Private	    :: Range -> Definitions	-> RawDefinitionI MaybeTypeSig TopLevel
	Postulate   :: Range -> [TypeSignature] -> RawDefinitionI MaybeTypeSig TopLevel
	Module	    :: Range -> Name -> Telescope -> Definitions
						-> RawDefinitionI MaybeTypeSig TopLevel
#endif

