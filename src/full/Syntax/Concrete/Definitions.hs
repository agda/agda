{-# OPTIONS -cpp -fglasgow-exts #-}

{-| In the concrete syntax the clauses of a function are not grouped together.
    Neither is the fixity declaration attached to its corresponding definition.
    This module defines the function to do this grouping and associate fixities
    with declarations rather than having them floating freely.
-}
module Syntax.Concrete.Definitions where

{-

What are the options?

- All in one go

    magic :: [Definition args] -> [BetterDefinition args]

  For this we also need a new kind of expression (for which local definitions
  are the better kind of definition). This would be done by parameterising the
  expression type.

  Alternatively we don't distinguish between Definition and BetterDefinition
  and just state the invariant. This doesn't follow the current design of
  having the type checker ensure these invariants.

- The view approach

    data Definitions (abstract)

    rawView :: Definitions -> [Definition]
    magic :: Definitions -> [BetterDefinition]

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

import Syntax.Concrete
import Syntax.Common
import Syntax.Position

{--------------------------------------------------------------------------
    Types
 --------------------------------------------------------------------------}

{-| The nice declarations. No fixity declarations and function definitions are
    contained in a single constructor instead of spread out between type
    signatures and clauses. The @private@ and @postulate@ modifiers have been
    distributed to the individual declarations. The type information obtained
    from using an inductive family for the concrete declarations is discarded
    here. The motivation is that it's easier to maintain correctness than to
    establish it and so the extra work of having an inductive family would not
    pay off here.
-}
data NiceDeclaration
	= Axiom Range Fixity Access Name Expr
	| FunDef Range Fixity Access Name (Maybe Expr) [Clause]
	| NiceData Range Fixity Access Name Telescope Expr [Constructor]
	| NiceMutual Range [NiceDeclaration]
	| NiceAbstract Range [NiceDeclaration]
	| NiceOpen Range QName [ImportDirective]
	| NiceNameSpace Range Name Expr [ImportDirective]
	| NiceImport Range QName [ImportDirective]
	| NiceModule Range QName Telescope [TopLevelDeclaration]

-- | In a nice expression, local declarations are nice.
type NiceExpr = Expr' NiceDeclaration

-- | One clause in a function definition.
data Clause = Clause LHS RHS WhereClause


{--------------------------------------------------------------------------
    The niceifier
 --------------------------------------------------------------------------}

class MakeNice a b where
    makeNice :: a -> b

instance MakeNice (Declaration typesig local private mutual abstract)
		  NiceDeclaration
	where

    makeNice = undefined

instance MakeNice Expr NiceExpr where
    makeNice = undefined
