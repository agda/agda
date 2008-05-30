
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
	| KwInfix | KwInfixL | KwInfixR | KwWith
	| KwSet | KwProp | KwForall | KwRecord | KwField
	| KwHiding | KwUsing | KwRenaming | KwTo | KwPublic
	| KwOPTIONS | KwBUILTIN | KwLINE
        | KwCOMPILED_DATA | KwCOMPILED | KwIMPORT
    deriving (Eq, Show)

layoutKeywords :: [Keyword]
layoutKeywords =
    [ KwLet, KwWhere, KwPostulate, KwMutual, KwAbstract, KwPrivate, KwPrimitive, KwField ]

data Symbol
	= SymDot | SymSemi | SymVirtualSemi | SymBar
	| SymColon | SymArrow | SymEqual | SymLambda
	| SymUnderscore	| SymQuestionMark   | SymAs
	| SymOpenParen	      | SymCloseParen
	| SymOpenBrace	      | SymCloseBrace
	| SymOpenVirtualBrace | SymCloseVirtualBrace
	| SymOpenPragma	      | SymClosePragma | SymEllipsis
    deriving (Eq, Show)

data Token
	  -- Keywords
	= TokKeyword Keyword Range
	  -- Identifiers and operators
	| TokId		(Range, String)
	| TokQId	[(Range, String)] -- non empty namespace
	  -- Literals
	| TokLiteral	Literal
	  -- Special symbols
	| TokSymbol Symbol Range
	  -- Other tokens
	| TokString (Range, String)  -- arbitrary string, used in pragmas
	| TokSetN (Range, Integer)
	| TokTeX (Range, String)
        | TokComment (Range, String)
	| TokDummy	-- Dummy token to make Happy not complain
			-- about overlapping cases.
	| TokEOF
    deriving (Eq, Show)

