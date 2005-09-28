
module Syntax.Parser.Tokens
    ( Token(..)
    , Keyword(..)
    , layoutKeywords
    , Symbol(..)
    ) where

import Syntax.Concrete (Name(..))
import Syntax.Position

data Keyword
	= KwLet | KwIn | KwWhere
	| KwPostulate | KwOpen | KwModule | KwData
	| KwInfix | KwInfixL | KwInfixR
	| KwMutual | KwAbstract | KwPrivate
	| KwSet | KwProp
    deriving (Eq, Show)

layoutKeywords :: [Keyword]
layoutKeywords = [ KwLet, KwWhere, KwPostulate, KwMutual, KwAbstract ]

data Symbol
	= SymDot | SymComma | SymSemi | SymVirtualSemi
	| SymBackQuote  | SymColon | SymArrow | SymEqual
	| SymUnderscore	| SymQuestionMark
	| SymOpenParen	      | SymCloseParen
	| SymOpenBrace	      | SymCloseBrace
	| SymOpenBracket      | SymCloseBracket
	| SymOpenVirtualBrace | SymCloseVirtualBrace
    deriving (Eq, Show)

data Token
	  -- Keywords
	= TokKeyword Keyword Range
	  -- Identifiers and operators
	| TokId		Name
	| TokOp		Name
	  -- Literals
	| TokLitString	(Range, String)
	| TokLitChar	(Range, Char)
	| TokLitInt	(Range, Integer)
	| TokLitFloat	(Range, Double)
	  -- Special symbols
	| TokSymbol Symbol Range
	  -- Other tokens
	| TokSetN (Range, Int)
	| TokTeX String
	| TokEOF
    deriving (Eq, Show)

