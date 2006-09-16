{-# OPTIONS -fglasgow-exts #-}

{-| Definitions for fixity and precedence levels.
-}
module Syntax.Fixity where

import Data.Generics (Typeable, Data)

import Syntax.Position
import Syntax.Common
import Syntax.Concrete.Name

data Operator = Operator NameDecl Fixity
    deriving (Typeable, Data, Show, Eq)

-- | Fixity of operators.
data Fixity = LeftAssoc  Range Int
	    | RightAssoc Range Int
	    | NonAssoc   Range Int
    deriving (Typeable, Data, Show)

instance Eq Fixity where
    LeftAssoc _ n   == LeftAssoc _ m	= n == m
    RightAssoc _ n  == RightAssoc _ m	= n == m
    NonAssoc _ n    == NonAssoc _ m	= n == m
    _		    == _		= False

fixityLevel :: Fixity -> Int
fixityLevel (LeftAssoc	_ n) = n
fixityLevel (RightAssoc _ n) = n
fixityLevel (NonAssoc	_ n) = n

-- | The default fixity. Currently defined to be @'LeftAssoc' 20@.
defaultFixity :: Fixity
defaultFixity = LeftAssoc noRange 20

defaultOperator :: Name -> Operator
defaultOperator x = Operator (NameDecl [x]) defaultFixity

-- | Precedence is associated with a context.
data Precedence = TopCtx | FunctionSpaceDomainCtx
		| LeftOperandCtx Fixity | RightOperandCtx Fixity
		| FunctionCtx | ArgumentCtx
    deriving (Show,Typeable,Data)

-- | The precedence corresponding to a possibly hidden argument.
hiddenArgumentCtx :: Hiding -> Precedence
hiddenArgumentCtx NotHidden = ArgumentCtx
hiddenArgumentCtx Hidden    = TopCtx

-- | Do we need to bracket an operator application of the given fixity
--   in a context with the given precedence.
opBrackets :: Operator -> Precedence -> Bool
opBrackets _ _ = True

-- | Does a lambda-like thing (lambda, let or pi) need brackets in the given
--   context. A peculiar thing with lambdas is that they don't need brackets
--   in a right operand context. For instance: @m >>= \x -> m'@ is a valid
--   infix application.
lamBrackets :: Precedence -> Bool
lamBrackets TopCtx		    = False
lamBrackets (RightOperandCtx _)  = False
lamBrackets _		    = True

-- | Does a function application need brackets?
appBrackets :: Precedence -> Bool
appBrackets ArgumentCtx	= True
appBrackets _		= False

-- | Does a function space need brackets?
piBrackets :: Precedence -> Bool
piBrackets TopCtx   = False
piBrackets _	    = True

instance HasRange Fixity where
    getRange (LeftAssoc  r _)	= r
    getRange (RightAssoc r _)	= r
    getRange (NonAssoc   r _)	= r

