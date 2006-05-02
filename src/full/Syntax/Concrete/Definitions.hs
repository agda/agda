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
module Syntax.Concrete.Definitions
    ( NiceDeclaration(..)
    , NiceDefinition(..)
    , NiceConstructor, NiceTypeSignature
    , Clause(..)
    , DeclarationException(..)
    , niceDeclarations
    ) where

import Control.Exception

import Data.Typeable
import qualified Data.Map as Map

import Syntax.Concrete
import Syntax.Common
import Syntax.Position
import Syntax.Fixity
import Syntax.Concrete.Pretty ()    -- need Show instance for Declaration

#include "../../undefined.h"

{--------------------------------------------------------------------------
    Types
 --------------------------------------------------------------------------}

{-| The nice declarations. No fixity declarations and function definitions are
    contained in a single constructor instead of spread out between type
    signatures and clauses. The @private@ and @postulate@ modifiers have been
    distributed to the individual declarations.
-}
data NiceDeclaration
	= Axiom Range Fixity Access Name Expr
	| Synonym Range Fixity Access Name Expr	WhereClause		    -- ^ Definition with no type signature: @x = e@
	| NiceDef Range [Declaration] [NiceTypeSignature] [NiceDefinition]
	    -- ^ A bunch of mutually recursive functions\/datatypes.
	    --   The last two lists have the same length. The first list is the
	    --   concrete declarations these definitions came from.
	| NiceAbstract Range [NiceDeclaration]
	| NiceModule Range Access QName Telescope [TopLevelDeclaration]
	| NiceModuleMacro Range Access Name Telescope Expr ImportDirective
	| NiceOpen Range QName ImportDirective
	| NiceImport Range QName (Maybe Name) ImportDirective

-- 	| NiceData Range Fixity Access Name Telescope Expr [NiceDeclaration]
-- 	| FunDef Range [Declaration] Fixity Access Name (Maybe Expr) [Clause]

-- | A definition without its type signature.
data NiceDefinition
	= FunDef  Range [Declaration] Fixity Access Name [Clause]
	| DataDef Range Fixity Access Name [LamBinding] [NiceConstructor]

-- | Only 'Axiom's.
type NiceConstructor = NiceDeclaration

-- | Only 'Axiom's.
type NiceTypeSignature	= NiceDeclaration

-- | One clause in a function definition.
data Clause = Clause LHS RHS WhereClause


-- | The exception type.
data DeclarationException
	= MultipleFixityDecls [(Name, [Fixity])]
	| MissingDefinition Name
	| BadSynonym Name [Declaration]
    deriving (Typeable, Show)

instance HasRange DeclarationException where
    getRange (MultipleFixityDecls xs) = getRange (fst $ head xs)
    getRange (MissingDefinition x)    = getRange x
    getRange (BadSynonym _ ds)	      = getRange ds

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

    Update the fixity map with usage counters? It would need to be a state
    monad rather than a reader monad in that case.
-}
niceDeclarations :: [Declaration] -> [NiceDeclaration]
niceDeclarations ds = nice (fixities ds) ds
    where

	-- If no fixity is given we return the default fixity.
	fixity = Map.findWithDefault defaultFixity

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
			([], _)	    -> __IMPOSSIBLE__
			(ds0,ds1)   -> mkFunDef fixs x Nothing ds0
					: nice fixs ds1

		_   -> nds ++ nice fixs ds
		    where
			nds = case d of
			    Data r x tel t cs   ->
				[ NiceDef r [d]
					    [ Axiom (fuseRange x t) f PublicAccess
						    x (foldr Pi t tel)
					    ]
					    [ DataDef (getRange cs) f PublicAccess x
						      (concatMap binding tel)
						      (niceAxioms fixs cs)
					    ]
				]
				where
				    f = fixity x fixs
				    binding (TypedBinding _ h xs _) =
					map (DomainFree h) xs

			    Mutual r ds ->
				[ mkMutual r [d] $
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

			    Module r x tel ds	->
				[ NiceModule r PublicAccess x tel ds ]

			    ModuleMacro r x tel e is ->
				[ NiceModuleMacro r PublicAccess x tel e is ]

			    Infix _ _		-> []
			    Open r x is		-> [NiceOpen r x is]
			    Import r x as is	-> [NiceImport r x as is]

			    _			-> __IMPOSSIBLE__
				-- FunClause and TypeSig have been taken care of


	-- Translate axioms
	niceAxioms :: Map.Map Name Fixity -> [TypeSignature] -> [NiceDeclaration]
	niceAxioms fixs ds = nice ds
	    where
		nice [] = []
		nice (d@(TypeSig x t) : ds) =
		    Axiom (getRange d) (fixity x fixs) PublicAccess x t
		    : nice ds
		nice _ = __IMPOSSIBLE__

	-- Create a function definition.
	mkFunDef fixs x Nothing ds@[FunClause (LHS r PrefixDef _ []) rhs wh] =
	    Synonym (getRange ds) (fixity x fixs) PublicAccess x rhs wh
	mkFunDef _ x Nothing ds	= throwDyn $ BadSynonym x ds
	mkFunDef fixs x (Just t) ds0 =
	    NiceDef (fuseRange x ds0)
		    (TypeSig x t : ds0)
		    [ Axiom (fuseRange x t) f PublicAccess x t ]
		    [ FunDef (getRange ds0) ds0 f PublicAccess x
			     (map mkClause ds0)
		    ]
	    where
		f  = fixity x fixs


	-- Turn a function clause into a nice function clause.
	mkClause (FunClause lhs rhs wh) = Clause lhs rhs wh
	mkClause _ = __IMPOSSIBLE__

	-- Check if a declaration is a definition of a particular function.
	isDefinitionOf x (FunClause (LHS _ _ y _) _ _)	= x == y
	isDefinitionOf x _				= False

	-- Make a mutual declaration
	mkMutual :: Range -> [Declaration] -> [NiceDeclaration] -> NiceDeclaration
	mkMutual r cs ds = setConcrete cs $ foldr smash (NiceDef r [] [] []) ds
	    where
		setConcrete cs (NiceDef r _ ts ds)  = NiceDef r cs ts ds
		setConcrete cs _		    = __IMPOSSIBLE__

		smash (NiceDef r0 _ ts0 ds0) (NiceDef r1 _ ts1 ds1) =
		    NiceDef (fuseRange r0 r1) [] (ts0 ++ ts1) (ds0 ++ ds1)
		smash _ _ = __IMPOSSIBLE__  -- only definitions can appear in a mutual

	-- Make a declaration private
	mkPrivate d =
	    case d of
		Axiom r f _ x e			-> Axiom r f PrivateAccess x e
		Synonym r f _ x e wh		-> Synonym r f PrivateAccess x e wh
		NiceDef r cs ts ds		-> NiceDef r cs (map mkPrivate ts)
								(map mkPrivateDef ds)
		NiceAbstract r ds		-> NiceAbstract r (map mkPrivate ds)
		NiceModule r _ x tel ds		-> NiceModule r PrivateAccess x tel ds
		NiceModuleMacro r _ x tel e is	-> NiceModuleMacro r PrivateAccess x tel e is
		_				-> d

	mkPrivateDef d =
	    case d of
		FunDef r ds f _ x cs	-> FunDef r ds f PrivateAccess x cs
		DataDef r f _ x ps cs	-> DataDef r f PrivateAccess x ps cs

-- | Add more fixities. Throw an exception for multiple fixity declarations.
plusFixities :: Map.Map Name Fixity -> Map.Map Name Fixity -> Map.Map Name Fixity
plusFixities m1 m2
    | Map.null isect	= Map.union m1 m2
    | otherwise		=
	throwDyn $ MultipleFixityDecls $ map decls (Map.keys isect)
    where
	isect	= Map.intersection m1 m2
	decls x = (x, map (Map.findWithDefault __IMPOSSIBLE__ x) [m1,m2])
				-- cpp doesn't know about primes

-- | Get the fixities from the current block. Doesn't go inside /any/ blocks.
--   The reason for this is that fixity declarations have to appear at the same
--   level (or possibly outside an abstract or mutual block) as its target
--   declaration.
fixities :: [Declaration] -> Map.Map Name Fixity
fixities (d:ds) =
    case d of
	Infix f xs  -> Map.fromList [ (x,f) | x <- xs ]
			`plusFixities` fixities ds
	_	    -> fixities ds
fixities [] = Map.empty

