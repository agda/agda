{-# OPTIONS -fglasgow-exts -cpp #-}

{-| The concrete syntax is a raw representation of the program text
    without any desugaring at all.  This is what the parser produces.
    The idea is that if we figure out how to keep the concrete syntax
    around, it can be printed exactly as the user wrote it.
-}
module Syntax.Concrete
    ( -- * Expressions
      Expr(..)
    , Name(..), QName(..)
    , Branch(..)
      -- * Bindings
    , LamBinding(..)
    , TypedBinding(..)
    , Telescope
      -- * Definitions
    , TopLevelDefinition
    , LocalDefinition
    , TypeSignature
    , Definition(..)
    , Local, TopLevel, MaybeTypeSig, OnlyTypeSig
    , Constructor
    , ImportDirective(..)
    , LHS, RHS, WhereClause
    )
    where

import Syntax.Position
import Syntax.Common

-- | A constructor declaration is just a type signature.
type Constructor = TypeSignature


-- | The raw view. Should represent exactly what the user wrote.
data Expr   = Ident QName			    -- ^ . @x@
	    | Lit Literal			    -- ^ . @1@ or @\"foo\"@
	    | QuestionMark Range		    -- ^ . @?@ or @{! ... !}@
	    | Underscore Range			    -- ^ . @_@
	    | App Range Hiding Expr Expr	    -- ^ . @e e@ or @e {e}@
	    | InfixApp Expr QName Expr		    -- ^ . @e + e@ (no hiding)
	    | Lam Range [LamBinding] Expr	    -- ^ . @\L -> e@
	    | Fun Range Hiding Expr Expr	    -- ^ . @e -> e@ or @{e} -> e@
	    | Pi TypedBinding Expr		    -- ^ . @(xs:e) -> e@ or @{xs:e} -> e@
	    | Set Range | Prop Range		    -- ^ . @Set, Prop@
	    | SetN Range Nat			    -- ^ . @Set0, Set1, ..@
	    | Let Range [LocalDefinition] Expr	    -- ^ . @let Ds in e@
	    | Elim Range Expr (Maybe Expr) [Branch] -- ^ . @by e with P of bs@
	    | Paren Range Expr			    -- ^ . @(e)@


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


-- | The things you are allowed to say when you shuffle names between name
--   spaces (i.e. in @import@, @namespace@, or @open@ declarations).
data ImportDirective
	= Hiding [Name]
	| Using  [Name]
	| Renaming [(Name, Name)]   -- ^ Contains @(oldName,newName)@ pairs.


-- | To be able to parse infix definitions properly left hand sides are parsed
--   as expressions. For instance, @x::xs ++ ys = x :: (xs ++ ys)@ should be a
--   valid definition of @++@ provided @::@ has higher precedence than @++@.
type LHS = Expr


type RHS	    = Expr
type WhereClause    = [LocalDefinition]


{--------------------------------------------------------------------------
    Definitions
 --------------------------------------------------------------------------}

data Local
data TopLevel
data OnlyTypeSig
data MaybeTypeSig

type LocalDefinition	= Definition MaybeTypeSig Local
type TypeSignature	= Definition OnlyTypeSig Local
type TopLevelDefinition = Definition MaybeTypeSig TopLevel


{-| Definition is family of datatypes indexed by the datakinds

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
data Definition typesig local
	= TypeSig Name Expr		    -- ^ . @Definition typesig local@
	| FunClause LHS RHS
	    WhereClause			    -- ^ . @Definition 'MaybeTypeSig' local@
	| Data Range Name Telescope
	    Expr [Constructor]		    -- ^ . @Definition 'MaybeTypeSig' local@
	| Mutual Range [LocalDefinition]    -- ^ . @Definition 'MaybeTypeSig' local@
	| Abstract Range [LocalDefinition]  -- ^ . @Definition 'MaybeTypeSig' local@
	| Open Range QName
	    [ImportDirective]		    -- ^ . @Definition 'MaybeTypeSig' local@
	| NameSpace Range QName Expr
	    [ImportDirective]		    -- ^ . @Definition 'MaybeTypeSig' local@
	| Import Range QName
	    [ImportDirective]		    -- ^ . @Definition 'MaybeTypeSig' 'TopLevel'@
	| Private Range [LocalDefinition]   -- ^ . @Definition 'MaybeTypeSig' 'TopLevel'@
	| Postulate Range [TypeSignature]   -- ^ . @Definition 'MaybeTypeSig' 'TopLevel'@
	| Module Range Name Telescope
	    [TopLevelDefinition]	    -- ^ . @Definition 'MaybeTypeSig' 'TopLevel'@

#else
-}
data Definition typesig local where

	TypeSig	    :: Name -> Expr
		    -> Definition typesig local

	FunClause   :: LHS -> RHS -> WhereClause
		    -> Definition MaybeTypeSig local

	Data	    :: Range -> Name -> Telescope -> Expr -> [Constructor] 
		    -> Definition MaybeTypeSig local

	Mutual	    :: Range -> [LocalDefinition]
		    -> Definition MaybeTypeSig local

	Abstract    :: Range -> [LocalDefinition]
		    -> Definition MaybeTypeSig local

	Open	    :: Range -> QName -> [ImportDirective]
		    -> Definition MaybeTypeSig local

	NameSpace   :: Range -> QName -> Expr -> [ImportDirective]
		    -> Definition MaybeTypeSig local

	Import	    :: Range -> QName -> [ImportDirective]
		    -> Definition MaybeTypeSig TopLevel

	Private	    :: Range -> [LocalDefinition]
		    -> Definition MaybeTypeSig TopLevel

	Postulate   :: Range -> [TypeSignature]
		    -> Definition MaybeTypeSig TopLevel

	Module	    :: Range -> Name -> Telescope -> [TopLevelDefinition]
		    -> Definition MaybeTypeSig TopLevel

#endif


{--------------------------------------------------------------------------
    Instances
 --------------------------------------------------------------------------}

instance HasRange Expr where
    getRange e =
	case e of
	    Ident x		-> getRange x
	    Lit x		-> getRange x
	    QuestionMark r	-> r
	    Underscore r	-> r
	    App r _ _ _		-> r
	    InfixApp e1 _ e2	-> fuseRange e1 e2
	    Lam r _ _		-> r
	    Fun r _ _ _		-> r
	    Pi b e		-> fuseRange b e
	    Set r		-> r
	    Prop r		-> r
	    SetN r _		-> r
	    Let r _ _		-> r
	    Elim r _ _ _	-> r
	    Paren r _		-> r

instance HasRange TypedBinding where
    getRange (TypedBinding r _ _ _) = r

