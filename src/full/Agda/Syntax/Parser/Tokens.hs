{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.Syntax.Parser.Tokens
    ( Token(..)
    , Keyword(..)
    , layoutKeywords
    , Symbol(..)
    ) where

import Agda.Syntax.Literal (RLiteral)
import Agda.Syntax.Position

data Keyword
        = KwLet | KwIn | KwWhere | KwData | KwCoData | KwDo
        | KwPostulate | KwAbstract | KwPrivate | KwInstance
        | KwInterleaved | KwMutual
        | KwOverlap
        | KwOpen | KwImport | KwModule | KwPrimitive | KwMacro
        | KwInfix | KwInfixL | KwInfixR | KwWith | KwRewrite
        | KwForall | KwRecord | KwConstructor | KwField
        | KwInductive | KwCoInductive
        | KwEta | KwNoEta
        | KwHiding | KwUsing | KwRenaming | KwTo | KwPublic
        | KwOpaque | KwUnfolding
        | KwOPTIONS | KwBUILTIN | KwLINE
        | KwFOREIGN | KwCOMPILE
        | KwIMPOSSIBLE | KwSTATIC | KwINJECTIVE | KwINLINE | KwNOINLINE
        | KwETA
        | KwNO_TERMINATION_CHECK | KwTERMINATING | KwNON_TERMINATING
        | KwNOT_PROJECTION_LIKE
        | KwNON_COVERING
        | KwWARNING_ON_USAGE | KwWARNING_ON_IMPORT
        | KwMEASURE | KwDISPLAY
        | KwREWRITE
        | KwQuote | KwQuoteTerm
        | KwUnquote | KwUnquoteDecl | KwUnquoteDef
        | KwSyntax
        | KwPatternSyn | KwTactic | KwCATCHALL
        | KwVariable
        | KwNO_POSITIVITY_CHECK | KwPOLARITY
        | KwNO_UNIVERSE_CHECK
    deriving (Eq, Show)

-- | Unconditional layout keywords.
--
-- Some keywords introduce layout only in certain circumstances,
-- these are not included here.
--
layoutKeywords :: [Keyword]
layoutKeywords =
    [ KwAbstract
    , KwDo
    , KwField
    , KwInstance
    , KwLet
    , KwMacro
    , KwMutual
    , KwPostulate
    , KwPrimitive
    , KwPrivate
    , KwVariable
    , KwWhere
    , KwOpaque
    ]

data Symbol
        = SymDot | SymSemi | SymVirtualSemi | SymBar
        | SymColon | SymArrow | SymEqual | SymLambda
        | SymUnderscore | SymQuestionMark   | SymAs
        | SymOpenParen        | SymCloseParen
        | SymOpenIdiomBracket | SymCloseIdiomBracket | SymEmptyIdiomBracket
        | SymDoubleOpenBrace  | SymDoubleCloseBrace
        | SymOpenBrace        | SymCloseBrace
        | SymOpenVirtualBrace | SymCloseVirtualBrace
        | SymOpenPragma       | SymClosePragma | SymEllipsis | SymDotDot
        | SymEndComment -- ^ A misplaced end-comment "-}".
    deriving (Eq, Show)

data Token
          -- Keywords
        = TokKeyword Keyword Interval
          -- Identifiers and operators
        | TokId         (Interval, String)
        | TokQId        [(Interval, String)]
                        -- Non-empty namespace. The intervals for
                        -- "A.B.x" correspond to "A.", "B." and "x".
          -- Literals
        | TokLiteral    RLiteral
          -- Special symbols
        | TokSymbol Symbol Interval
          -- Other tokens
        | TokString (Interval, String)
            -- ^ Arbitrary string (not enclosed in double quotes), used in pragmas.
        | TokTeX (Interval, String)
        | TokMarkup (Interval, String)
        | TokComment (Interval, String)
        | TokDummy      -- Dummy token to make Happy not complain
                        -- about overlapping cases.
        | TokEOF Interval
    deriving (Eq, Show)

instance HasRange Token where
  getRange (TokKeyword _ i)    = getRange i
  getRange (TokId (i, _))      = getRange i
  getRange (TokQId iss)        = getRange (map fst iss)
  getRange (TokLiteral lit)    = getRange lit
  getRange (TokSymbol _ i)     = getRange i
  getRange (TokString (i, _))  = getRange i
  getRange (TokTeX (i, _))     = getRange i
  getRange (TokMarkup (i, _))  = getRange i
  getRange (TokComment (i, _)) = getRange i
  getRange TokDummy            = noRange
  getRange (TokEOF i)          = getRange i
