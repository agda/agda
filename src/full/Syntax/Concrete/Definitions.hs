{-# OPTIONS -cpp -fglasgow-exts #-}

{-| In the concrete syntax the clauses of a function are not grouped together.
    Neither is the fixity declaration attached to its corresponding definition.
    This module defines the function to do this grouping and associate fixities
    with declarations rather than having them floating freely.

Thoughts:

What are the options?

- All in one go

    > magic :: [Definition args] -> [BetterDefinition args]

  For this we also need a new kind of expression (for which local definitions
  are the better kind of definition). This would be done by parameterising the
  expression type.

  Alternatively we don't distinguish between Definition and BetterDefinition
  and just state the invariant. This doesn't follow the current design of
  having the type checker ensure these invariants.

- The view approach

    > data Definitions (abstract)
    > 
    > rawView :: Definitions -> [Definition]
    > magic :: Definitions -> [BetterDefinition]

  The advantage here is that we can let the kind of local definitions in
  expressions be the abstract Definitions, so we only need one kind of
  expression.

  The disadvantage would be that we have to call the view all the time. All the
  time would be... when translating to abstract syntax and rotating infix
  stuff. Infix rotation has to be done after scope analysis, and since there
  won't be any parenthesis in the abstract syntax, it's probably easiest to do
  it at the same time.

  Actually, since the abstract thing definition would just be the raw
  definition we could skip the view business and write the magic function that
  just transforms the top-level list of definitions.


  Hm... at the moment, left hand sides are parsed as expressions. The idea is
  that when we know the fixities of the operators we can turn this expression
  into a proper left hand side. The problem with this is that we have to sort
  out the fixities before even knowing what name a particular clause defines.
  The current idea, to first group the definitions and then rotate infix
  applications, won't work. The solution is to make sure that we always know
  which name is being defined.

  Ok, representation of left hand sides are not expressions anymore and we
  always now which name a left hand side defines.

-}
module Syntax.Concrete.Definitions where

{-

-}

import Control.Exception

import Data.Typeable

import Syntax.Concrete
import Syntax.Common
import Syntax.Position

import Utils.Map

#include "undefined.h"

{--------------------------------------------------------------------------
    Types
 --------------------------------------------------------------------------}

{-| The nice declarations. No fixity declarations and function definitions are
    contained in a single constructor instead of spread out between type
    signatures and clauses. The @private@ and @postulate@ modifiers have been
    distributed to the individual declarations. The type information obtained
    from using an (fake) inductive family for the concrete declarations is
    discarded here. The motivation is that it's easier to maintain correctness
    than to establish it and so the extra work of having an inductive family
    would not pay off here.
-}
data NiceDeclaration
	= Axiom Range Fixity Access Name NiceExpr
	| FunDef Range Fixity Access Name (Maybe NiceExpr) [Clause]
	| NiceData Range Fixity Access Name NiceTelescope NiceExpr [NiceConstructor]
	| NiceMutual Range [NiceDeclaration]
	| NiceAbstract Range [NiceDeclaration]
	| NiceOpen Range QName [ImportDirective]
	| NiceNameSpace Range Name NiceExpr [ImportDirective]
	| NiceImport Range QName [ImportDirective]
	| NiceModule Range Access QName NiceTelescope [NiceDeclaration]

-- | In a nice expression local declarations are nice.
type NiceExpr = Expr' [NiceDeclaration]

-- | One clause in a function definition.
data Clause = Clause LHS NiceRHS NiceWhereClause

type NiceRHS		= RHS' [NiceDeclaration]
type NiceWhereClause	= WhereClause' [NiceDeclaration]
type NiceTelescope	= Telescope' [NiceDeclaration]

-- | Alway 'Axiom'.
type NiceConstructor	= NiceDeclaration

-- | The exception type.
data DeclarationException
	= MultipleFixityDecls [(Name, [Fixity])]
	| MissingDefinition Name
    deriving (Typeable)

{--------------------------------------------------------------------------
    The niceifier
 --------------------------------------------------------------------------}

{-| How to fail? We need to give a nice error message. Intuitively it should be
    a parse error. Put it in the parse monad?

    It would be nice to have a general mechanism. Lots of things fail
    (parsing, type checking, translation...), how to handle this uniformly?
    Control.Monad.Error? What would the error object be?

    Niklas suggested using exceptions. Can be thrown by a pure function but
    have to be caught in IO. The advantage is that things whose only side
    effect is the possibility of failure doesn't need a monad. If one uses
    dynamic exceptions each function can define it's own exception type in a
    modular way.

    The disadvantage is that the type won't reflect the fact that the function
    might throw an exception.

    Let's go with that.

    TODO: check that every fixity declaration has a corresponding definition.
    How to do this?
-}
niceDeclarations :: [Declaration'] -> [NiceDeclaration]
niceDeclarations ds = nice (fixities ds) ds
    where

	-- If no fixity is given we return the default fixity.
	fixity = lookupMap' defaultFixity

	-- We forget all fixities in recursive calls. This is because
	-- fixity declarations have to appear at the same level as the
	-- declaration.
	fmapNice x = fmap niceDeclarations x

	nice _ []	 = []
	nice fixs (d:ds) =
	    case d of
		TypeSig x t ->
		    -- After a type signature there should follow a bunch of
		    -- clauses.
		    case span (isDefinitionOf x) ds of
			([], _)	    -> throwDyn $ MissingDefinition x
			(ds0,ds1)   -> mkFunDef fixs x (Just t) ds0
					: nice fixs ds1

		FunClause (LHS _ _ x _) _ _ ->
		    -- If we see a function clause at this point, there
		    -- was no corresponding type signature.
		    case span (isDefinitionOf x) (d:ds) of
			([], _)	    -> __UNDEFINED__
			(ds0,ds1)   -> mkFunDef fixs x Nothing ds0
					: nice fixs ds1

		_   -> nds ++ nice fixs ds
		    where
			nds = case d of
			    Data r x tel t cs   ->
				[ NiceData r (fixity x fixs) PublicDecl
					 x (map fmapNice tel)
					 (fmapNice t) (niceAxioms fixs cs)
				]

			    Mutual r ds ->
				[ NiceMutual r $
				    nice (fixities ds `plusFixities` fixs) ds
				]

			    Abstract r ds ->
				[ NiceAbstract r $
				    nice (fixities ds `plusFixities` fixs) ds
				]

			    Private _ ds ->
				map mkPrivate
				$ nice (fixities ds `plusFixities` fixs) ds

			    Postulate _ ds -> niceAxioms fixs ds

			    Open r m is		-> [NiceOpen r m is]
			    NameSpace r m e is	-> [NiceNameSpace r m
							(fmapNice e) is
						   ]
			    Import r m is	-> [NiceImport r m is]
			    Module r x tel ds	->
				[ NiceModule r PublicDecl x (map fmapNice tel)
				    (niceDeclarations ds)
				]

			    Infix _ _   -> __UNDEFINED__

			    _   -> undefined

	-- Translate axioms
	niceAxioms fixs [] = []
	niceAxioms fixs (d@(TypeSig x t) : ds) =
	    Axiom (getRange d) (fixity x fixs) PublicDecl x (fmapNice t)
	    : niceAxioms fixs ds
	niceAxioms _ _ = __UNDEFINED__

	-- Create a function definition.
	mkFunDef fixs x mt ds0 =
	    FunDef (fuseRange x ds0) (fixity x fixs)
		   PublicDecl x (fmap fmapNice mt)
		   (map mkClause ds0)

	-- Turn a function clause into a nice function clause.
	mkClause (FunClause lhs rhs wh) =
	    Clause lhs (fmapNice rhs)
		       (niceDeclarations wh)
	mkClause _ = __UNDEFINED__

	-- Check if a declaration is a definition of a particular function.
	isDefinitionOf x (FunClause (LHS _ _ y _) _ _)	= x == y
	isDefinitionOf x _				= False

	-- Make a declaration private
	mkPrivate d =
	    case d of
		Axiom r f _ x e		  -> Axiom r f PrivateDecl x e
		FunDef r f _ x t cs	  -> FunDef r f PrivateDecl x t cs
		NiceData r f _ x tel s cs -> NiceData r f PrivateDecl x tel s $
						map mkPrivate cs
		NiceMutual r ds		  -> NiceMutual r (map mkPrivate ds)
		NiceAbstract r ds	  -> NiceAbstract r (map mkPrivate ds)
		NiceModule r _ x tel ds	  -> NiceModule r PrivateDecl x tel ds
		_			  -> d


-- | Add more fixities. Throw an exception for multiple fixity declarations.
plusFixities :: Map Name Fixity -> Map Name Fixity -> Map Name Fixity
plusFixities m1 m2
    | isEmptyMap isect	= plusMap m1 m2
    | otherwise		=
	throwDyn $ MultipleFixityDecls $ map decls (keysMap isect)
    where
	isect	= intersectMap m1 m2
	decls x = (x, map (lookupMap' {-'-} __UNDEFINED__ x) [m1,m2])
				-- cpp doesn't know about primes

-- | Get the fixities from the current block. Doesn't go inside /any/ blocks.
--   The reason for this is that fixity declarations have to appear at the same
--   level (or possibly outside an abstract or mutual block) as its target
--   declaration.
fixities :: [Declaration'] -> Map Name Fixity
fixities (d:ds) =
    case d of
	Infix f xs  -> buildMap [ (x,f) | x <- xs ]
			`plusFixities` fixities ds
	_	    -> fixities ds
fixities [] = emptyMap

