{-# LANGUAGE CPP, DeriveDataTypeable #-}

{-| Definitions for fixity and precedence levels.
-}
module Agda.Syntax.Fixity where

import Data.Generics (Typeable, Data)

import Agda.Syntax.Position
import Agda.Syntax.Common
import Agda.Syntax.Concrete.Name
import Agda.Syntax.Notation

-- | The notation is handled as the fixity in the renamer. Hence they
-- are grouped together in this type.
data Fixity' = Fixity' 
    {theFixity :: Fixity,
     theNotation :: Notation}
  deriving (Typeable, Data, Show, Eq)

-- | All the notation information related to a name.
type NewNotation = (Name, Fixity, Notation)

-- | If an operator has no specific notation, recover it from its name.
oldToNewNotation :: (Name, Fixity') -> NewNotation
oldToNewNotation (name, Fixity' f []) = (name, f, syntaxOf name)
oldToNewNotation (name, Fixity' f syn) = (name, f, syn)

syntaxOf :: Name -> Notation
syntaxOf (NoName _ _) = []
syntaxOf (Name _ [_]) = []
syntaxOf (Name _ xs)  = mkSyn 0 xs
 where mkSyn :: Int -> [NamePart] -> Notation
       mkSyn n [] = []
       mkSyn n (Hole:xs) = NormalHole n : mkSyn (1+n) xs
       mkSyn n (Id x:xs) = IdPart x : mkSyn n xs


defaultFixity' = Fixity' defaultFixity defaultNotation

noFixity = NonAssoc noRange (negate 666) 

-- | Fixity of operators.
data Fixity = LeftAssoc  Range Nat
	    | RightAssoc Range Nat
	    | NonAssoc   Range Nat
    deriving (Typeable, Data, Show)

instance Eq Fixity where
    LeftAssoc _ n   == LeftAssoc _ m	= n == m
    RightAssoc _ n  == RightAssoc _ m	= n == m
    NonAssoc _ n    == NonAssoc _ m	= n == m
    _		    == _		= False

fixityLevel :: Fixity -> Nat
fixityLevel (LeftAssoc	_ n) = n
fixityLevel (RightAssoc _ n) = n
fixityLevel (NonAssoc	_ n) = n

-- | The default fixity. Currently defined to be @'NonAssoc' 20@.
defaultFixity :: Fixity
defaultFixity = NonAssoc noRange 20

-- | Precedence is associated with a context.
data Precedence = TopCtx | FunctionSpaceDomainCtx
		| LeftOperandCtx Fixity | RightOperandCtx Fixity
		| FunctionCtx | ArgumentCtx | InsideOperandCtx
                | WithFunCtx | WithArgCtx | DotPatternCtx
    deriving (Show,Typeable,Data)


-- | The precedence corresponding to a possibly hidden argument.
hiddenArgumentCtx :: Hiding -> Precedence
hiddenArgumentCtx NotHidden = ArgumentCtx
hiddenArgumentCtx Hidden    = TopCtx

-- | Do we need to bracket an operator application of the given fixity
--   in a context with the given precedence.
opBrackets :: Fixity -> Precedence -> Bool
opBrackets (LeftAssoc _ n1)
           (LeftOperandCtx   (LeftAssoc   _ n2)) | n1 >= n2       = False
opBrackets (RightAssoc _ n1)
           (RightOperandCtx  (RightAssoc  _ n2)) | n1 >= n2       = False
opBrackets f1
           (LeftOperandCtx  f2) | fixityLevel f1 > fixityLevel f2 = False
opBrackets f1
           (RightOperandCtx f2) | fixityLevel f1 > fixityLevel f2 = False
opBrackets _ TopCtx = False
opBrackets _ FunctionSpaceDomainCtx = False
opBrackets _ InsideOperandCtx	    = False
opBrackets _ WithArgCtx             = False
opBrackets _ WithFunCtx             = False
opBrackets _ _			    = True

-- | Does a lambda-like thing (lambda, let or pi) need brackets in the given
--   context. A peculiar thing with lambdas is that they don't need brackets
--   in a right operand context. For instance: @m >>= \x -> m'@ is a valid
--   infix application.
lamBrackets :: Precedence -> Bool
lamBrackets TopCtx		= False
lamBrackets (RightOperandCtx _) = False
lamBrackets _			= True

-- | Does a function application need brackets?
appBrackets :: Precedence -> Bool
appBrackets ArgumentCtx   = True
appBrackets DotPatternCtx = True
appBrackets _             = False

-- | Does a with application need brackets?
withAppBrackets :: Precedence -> Bool
withAppBrackets TopCtx                 = False
withAppBrackets FunctionSpaceDomainCtx = False
withAppBrackets WithFunCtx             = False
withAppBrackets _                      = True

-- | Does a function space need brackets?
piBrackets :: Precedence -> Bool
piBrackets TopCtx   = False
piBrackets _	    = True

roundFixBrackets :: Precedence -> Bool
roundFixBrackets DotPatternCtx = True
roundFixBrackets _ = False

instance HasRange Fixity where
    getRange (LeftAssoc  r _)	= r
    getRange (RightAssoc r _)	= r
    getRange (NonAssoc   r _)	= r

