
module Syntax.Parser.Tokens
    ( Token(..)
    , Keyword(..)
    , layoutKeywords
    , Symbol(..)
    ) where

import Syntax.Literal (Literal)
import Syntax.Concrete.Name (Name, QName)
import Syntax.Position

data Keyword
	= KwLet | KwIn | KwWhere | KwData
	| KwPostulate | KwMutual | KwAbstract | KwPrivate
	| KwOpen | KwImport | KwModule | KwPrimitive
	| KwInfix | KwInfixL | KwInfixR
	| KwSet | KwProp | KwForall
	| KwHiding | KwUsing | KwRenaming | KwTo
	| KwOPTIONS | KwBUILTIN
    deriving (Eq, Show)

layoutKeywords :: [Keyword]
layoutKeywords =
    [ KwLet, KwWhere, KwPostulate, KwMutual, KwAbstract, KwPrivate, KwPrimitive ]

data Symbol
	= SymDot | SymComma | SymSemi | SymVirtualSemi
	| SymBackQuote  | SymColon | SymArrow | SymEqual | SymLambda
	| SymUnderscore	| SymQuestionMark   | SymAs
	| SymOpenParen	      | SymCloseParen
	| SymOpenBrace	      | SymCloseBrace
	| SymOpenBracket      | SymCloseBracket
	| SymOpenVirtualBrace | SymCloseVirtualBrace
	| SymOpenPragma	      | SymClosePragma
    deriving (Eq, Show)

data Token
	  -- Keywords
	= TokKeyword Keyword Range
	  -- Identifiers and operators
	| TokId		Name
	| TokQId	QName	-- non empty namespace
	  -- Literals
	| TokLiteral	Literal
	  -- Special symbols
	| TokSymbol Symbol Range
	  -- Other tokens
	| TokString String  -- arbitrary string, used in pragmas
	| TokSetN (Range, Int)
	| TokTeX String
	| TokDummy	-- Dummy token to make Happy not complain
			-- about overlapping cases.
	| TokEOF
    deriving (Eq, Show)

