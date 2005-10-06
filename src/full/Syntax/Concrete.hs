{-# OPTIONS -fglasgow-exts -cpp #-}

{-| The concrete syntax is a raw representation of the program text
    without any desugaring at all.  This is what the parser produces.
    The idea is that if we figure out how to keep the concrete syntax
    around, it can be printed exactly as the user wrote it.
-}
module Syntax.Concrete
    ( -- * Expressions
      Expr'(..), Expr
    , Name(..), QName(..)
    , Branch(..)
      -- * Bindings
    , LamBinding(..)
    , TypedBinding(..)
    , Telescope
      -- * Declarations
    , Declaration, Declaration'(..)
    , Local, TypeSig, Private, Mutual, Abstract, DontCare
    , TopLevelDeclaration
    , TypeSignature
    , LocalDeclaration, PrivateDeclaration
    , MutualDeclaration, AbstractDeclaration
    , typeSig, funClause, dataDecl, infixDecl, mutual, abstract
    , private, postulate, open, nameSpace, importDecl, moduleDecl
    , Constructor
    , Fixity(..)
    , defaultFixity
    , ImportDirective(..)
    , LHS(..), Argument(..), Pattern(..)
    , RHS, WhereClause
    )
    where

import Data.Generics hiding (Fixity, Infix)

import Syntax.Position
import Syntax.Common

-- | A constructor declaration is just a type signature.
type Constructor = TypeSignature


-- | Concrete expressions. Should represent exactly what the user wrote.
--   Parameterised over the type of local declarations.
data Expr' local
	= Ident QName						    -- ^ . @x@
	| Lit Literal						    -- ^ . @1@ or @\"foo\"@
	| QuestionMark Range					    -- ^ . @?@ or @{! ... !}@
	| Underscore Range					    -- ^ . @_@
	| App Range Hiding (Expr' local) (Expr' local)		    -- ^ . @e e@ or @e {e}@
	| InfixApp (Expr' local) QName (Expr' local)		    -- ^ . @e + e@ (no hiding)
	| Lam Range [LamBinding] (Expr' local)			    -- ^ . @\L -> e@
	| Fun Range Hiding (Expr' local) (Expr' local)		    -- ^ . @e -> e@ or @{e} -> e@
	| Pi TypedBinding (Expr' local)				    -- ^ . @(xs:e) -> e@ or @{xs:e} -> e@
	| Set Range | Prop Range				    -- ^ . @Set, Prop@
	| SetN Range Nat					    -- ^ . @Set0, Set1, ..@
	| Let Range [local] (Expr' local)			    -- ^ . @let Ds in e@
	| Elim Range (Expr' local) (Maybe (Expr' local)) [Branch]   -- ^ . @by e with P of bs@
	| Paren Range (Expr' local)				    -- ^ . @(e)@
    deriving (Typeable, Data, Eq, Show)

-- | Concrete expressions. Local declarations are 'LocalDeclaration's.
type Expr = Expr' LocalDeclaration


-- | Concrete patterns. No literals in patterns at the moment.
data Pattern
	= IdentP QName
	| AppP Pattern Pattern
	| InfixAppP Pattern QName Pattern
	| ParenP Range Pattern
    deriving (Typeable, Data, Eq, Show)


-- | A (fancy) case branch is on the form @p1 .. pn -> e@ where @pi@ are arbitrary
--   expressions.
data Branch = Branch [Expr] Expr
    deriving (Typeable, Data, Eq, Show)


-- | A lambda binding is either domain free or typed.
data LamBinding
	= DomainFree Hiding Name		-- ^ . @x@ or @{x}@
	| DomainFull TypedBinding		-- ^ . @(xs:e)@ or @{xs:e}@
    deriving (Typeable, Data, Eq, Show)


-- | A typed binding. Appears in dependent function spaces, typed lambdas, and
--   telescopes.
data TypedBinding
	= TypedBinding Range Hiding [Name] Expr -- (xs:e) or {xs:e}
    deriving (Typeable, Data, Eq, Show)


-- | A telescope is a sequence of typed bindings. Bound variables are in scope
--   in later types.
type Telescope = [TypedBinding]


-- | The things you are allowed to say when you shuffle names between name
--   spaces (i.e. in @import@, @namespace@, or @open@ declarations).
data ImportDirective
	= Hiding [Name]
	| Using  [Name]
	| Renaming [(Name, Name)]   -- ^ Contains @(oldName,newName)@ pairs.
    deriving (Typeable, Data, Show, Eq)


{-| Left hand sides can be written in infix style. For example:

    > n + suc m = suc (n + m)
    > (f . g) x = f (g x)

    It must always be clear which name is defined, independently of fixities.
    Hence the following definition is never ok:

    > x::xs ++ ys = x :: (xs ++ ys)

-}
data LHS = LHS Range IsInfix Name [Argument]
    deriving (Typeable, Data, Show, Eq)

-- | An function argument is a pattern which might be hidden.
data Argument = Argument Hiding Pattern
    deriving (Typeable, Data, Show, Eq)


type RHS	    = Expr
type WhereClause    = [LocalDeclaration]


{--------------------------------------------------------------------------
    Declarations
 --------------------------------------------------------------------------}

data Local
data TypeSig
data Private
data Mutual
data Abstract
data DontCare

-- | Just type signatures.
type TypeSignature	 = Declaration TypeSig DontCare DontCare DontCare DontCare

-- | Declarations that can appear in a 'Let' or a 'WhereClause'.
type LocalDeclaration	 = Declaration DontCare Local DontCare DontCare DontCare

-- | Declarations that can appear in a 'Private' block.
type PrivateDeclaration	 = Declaration DontCare DontCare Private DontCare DontCare

-- | Declarations that can appear in a 'Mutual' block.
type MutualDeclaration	 = Declaration DontCare DontCare DontCare Mutual DontCare

-- | Declarations that can appear in a 'Abstract' block.
type AbstractDeclaration = Declaration DontCare DontCare DontCare DontCare Abstract

-- | Everything can appear at top-level.
type TopLevelDeclaration = Declaration DontCare DontCare DontCare DontCare DontCare

-- | Fixity of infix operators.
data Fixity = LeftAssoc Integer | RightAssoc Integer | NonAssoc Integer
    deriving (Typeable, Data, Show, Eq)

-- | The default fixity. Currently defined to be @'LeftAssoc' 20@.
defaultFixity :: Fixity
defaultFixity = LeftAssoc 20

{-| Declaration is a family of datatypes indexed by the datakinds

    @
    datakind TypeSig  = 'TypeSig' | 'DontCare'
    datakind Local    = 'Local' | 'DontCare'
    datakind Private  = 'Private' | 'DontCare'
    datakind Mutual   = 'Mutual' | 'DontCare'
    datakind Abstract = 'Abstract' | 'DontCare'
    @

    Of course, there is no such thing as a @datakind@ in Haskell, so we just
    define phantom types for the intended constructors.  The indices should be
    interpreted as follows: The type indexed by 'Local' contains only the
    declarations that can appear in a local declaration. If the index is
    'DontCare' the type contains all declarations regardless of whether they can
    appear in a local declaration.  There is no grouping of function clauses
    and\/or type signatures in the concrete syntax. That happens in
    "Syntax.Concrete.Definitions".

    We could use a real inductive family (from ghc 6.4) to do this, but since 
    they don't work with the deriving mechanism, and is not supported by older
    versions of the compiler we use the poor man's version of using type
    synonyms and constructor functions.
-}
type Declaration typesig local private mutual abstract = Declaration'

{-| The representation type of a declaration. The comments indicate the which
    type in the intended family the constructor targets.
-}
data Declaration'
	= TypeSig Name Expr		    -- ^ . @Declaration typesig local private mutual abstract@
	| FunClause LHS RHS
	    WhereClause			    -- ^ . @Declaration 'DontCare' local private mutual abstract@
	| Data Range Name Telescope
	    Expr [Constructor]		    -- ^ . @Declaration 'DontCare' local private mutual abstract@
	| Infix Range Fixity [Name]	    -- ^ . @Declaration 'DontCare' local private mutual abstract@
	| Mutual Range [MutualDeclaration]  -- ^ . @Declaration 'DontCare' local private 'DontCare' abstract@
	| Abstract Range [LocalDeclaration] -- ^ . @Declaration 'DontCare' local private 'DontCare' 'DontCare'@
	| Private Range [PrivateDeclaration]-- ^ . @Declaration 'DontCare' 'DontCare' 'DontCare' 'DontCare' 'DontCare'@
	| Postulate Range [TypeSignature]   -- ^ . @Declaration 'DontCare' 'DontCare' private 'DontCare' 'DontCare'@
	| Open Range QName
	    [ImportDirective]		    -- ^ . @Declaration 'DontCare' local private 'DontCare' abstract@
	| NameSpace Range Name Expr
	    [ImportDirective]		    -- ^ . @Declaration 'DontCare' local private 'DontCare' abstract@
	| Import Range QName
	    [ImportDirective]		    -- ^ . @Declaration 'DontCare' 'DontCare' 'DontCare' 'DontCare' 'DontCare'@
	| Module Range QName Telescope
	    [TopLevelDeclaration]	    -- ^ . @Declaration 'DontCare' 'DontCare' private 'DontCare' 'DontCare'@
    deriving (Eq, Show, Typeable, Data)


typeSig	:: Name -> Expr -> Declaration typesig local private mutual abstract
typeSig = TypeSig

funClause :: LHS -> RHS -> WhereClause -> Declaration DontCare local private mutual abstract
funClause = FunClause

dataDecl :: Range -> Name -> Telescope -> Expr -> [Constructor]  -> Declaration DontCare local private mutual abstract
dataDecl = Data

infixDecl :: Range -> Fixity -> [Name] -> Declaration DontCare local private mutual abstract
infixDecl = Infix

mutual :: Range -> [MutualDeclaration] -> Declaration DontCare local private DontCare abstract
mutual = Mutual

abstract :: Range -> [AbstractDeclaration] -> Declaration DontCare local private DontCare DontCare
abstract = Abstract

private	:: Range -> [PrivateDeclaration] -> Declaration DontCare DontCare DontCare DontCare DontCare
private = Private

postulate :: Range -> [TypeSignature] -> Declaration DontCare DontCare private DontCare DontCare
postulate = Postulate

open :: Range -> QName -> [ImportDirective] -> Declaration DontCare local private DontCare abstract
open = Open

nameSpace :: Range -> Name -> Expr -> [ImportDirective] -> Declaration DontCare local private DontCare abstract
nameSpace = NameSpace

importDecl :: Range -> QName -> [ImportDirective] -> Declaration DontCare DontCare DontCare DontCare DontCare
importDecl = Import

moduleDecl :: Range -> QName -> Telescope -> [TopLevelDeclaration] -> Declaration DontCare DontCare private DontCare DontCare
moduleDecl = Module


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

instance HasRange LamBinding where
    getRange (DomainFree _ x)	= getRange x
    getRange (DomainFull b)	= getRange b

instance HasRange Declaration' where
    getRange (TypeSig x t)	    = fuseRange x t
    getRange (FunClause lhs rhs []) = fuseRange lhs rhs
    getRange (FunClause lhs rhs wh) = fuseRange lhs (last wh)
    getRange (Data r _ _ _ _)	    = r
    getRange (Mutual r _)	    = r
    getRange (Abstract r _)	    = r
    getRange (Open r _ _)	    = r
    getRange (NameSpace r _ _ _)    = r
    getRange (Import r _ _)	    = r
    getRange (Private r _)	    = r
    getRange (Postulate r _)	    = r
    getRange (Module r _ _ _)	    = r

instance HasRange ImportDirective where
    getRange (Using xs)	    = getRange xs
    getRange (Hiding xs)    = getRange xs
    getRange (Renaming xs)  = getRange xs

instance HasRange LHS where
    getRange (LHS r _ _ _)  = r

