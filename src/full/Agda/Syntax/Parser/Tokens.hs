
module Agda.Syntax.Parser.Tokens
    ( Token(..)
    , Keyword(..)
    , layoutKeywords
    , Symbol(..)
    ) where

import Agda.Syntax.Literal (Literal)
import Agda.Syntax.Concrete.Name (Name, QName)
import Agda.Syntax.Position

data Keyword
	= KwLet | KwIn | KwWhere | KwData | KwCoData
	| KwPostulate | KwMutual | KwAbstract | KwPrivate
	| KwOpen | KwImport | KwModule | KwPrimitive
	| KwInfix | KwInfixL | KwInfixR | KwWith | KwRewrite
	| KwSet | KwProp | KwForall | KwRecord | KwConstructor | KwField
        | KwInductive | KwCoInductive
	| KwHiding | KwUsing | KwRenaming | KwTo | KwPublic
	| KwOPTIONS | KwBUILTIN | KwLINE
	| KwCOMPILED_DATA | KwCOMPILED_TYPE | KwCOMPILED | KwCOMPILED_EPIC | KwCOMPILED_JS
	| KwIMPORT | KwIMPOSSIBLE | KwETA | KwNO_TERMINATION_CHECK | KwSTATIC
	| KwQuoteGoal | KwQuote | KwQuoteTerm | KwUnquote | KwSyntax | KwPatternSyn
    deriving (Eq, Show)

layoutKeywords :: [Keyword]
layoutKeywords =
    [ KwLet, KwWhere, KwPostulate, KwMutual, KwAbstract, KwPrivate, KwPrimitive, KwField ]

data Symbol
	= SymDot | SymSemi | SymVirtualSemi | SymBar
	| SymColon | SymArrow | SymEqual | SymLambda
	| SymUnderscore	| SymQuestionMark   | SymAs
	| SymOpenParen	      | SymCloseParen
	| SymDoubleOpenBrace  | SymDoubleCloseBrace
	| SymOpenBrace	      | SymCloseBrace
	| SymOpenVirtualBrace | SymCloseVirtualBrace
	| SymOpenPragma	      | SymClosePragma | SymEllipsis | SymDotDot
--        | SymColonBrace
    deriving (Eq, Show)

data Token
	  -- Keywords
	= TokKeyword Keyword Interval
	  -- Identifiers and operators
	| TokId		(Interval, String)
	| TokQId	[(Interval, String)]
                        -- Non-empty namespace. The intervals for
                        -- "A.B.x" correspond to "A.", "B." and "x".
	  -- Literals
	| TokLiteral	Literal
	  -- Special symbols
	| TokSymbol Symbol Interval
	  -- Other tokens
	| TokString (Interval, String)  -- arbitrary string, used in pragmas
	| TokSetN (Interval, Integer)
	| TokTeX (Interval, String)
        | TokComment (Interval, String)
	| TokDummy	-- Dummy token to make Happy not complain
			-- about overlapping cases.
	| TokEOF
    deriving (Eq, Show)

instance HasRange Token where
  getRange (TokKeyword _ i)    = getRange i
  getRange (TokId (i, _))      = getRange i
  getRange (TokQId iss)        = Range $ map fst iss
  getRange (TokLiteral lit)    = getRange lit
  getRange (TokSymbol _ i)     = getRange i
  getRange (TokString (i, _))  = getRange i
  getRange (TokSetN (i, _))    = getRange i
  getRange (TokTeX (i, _))     = getRange i
  getRange (TokComment (i, _)) = getRange i
  getRange TokDummy            = noRange
  getRange TokEOF              = noRange
