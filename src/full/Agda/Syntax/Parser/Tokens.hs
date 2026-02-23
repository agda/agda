{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.Syntax.Parser.Tokens
    ( Token(.., TokQual)
    , QualifiableToken(..), QualifiedToken(..)
    , Keyword(..)
    , layoutKeywords
    , Symbol(..)
    ) where

import Data.Functor (void)

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
        | KwIMPOSSIBLE | KwSTATIC | KwINJECTIVE | KwINJECTIVE_FOR_INFERENCE | KwINLINE | KwNOINLINE
        | KwETA
        | KwNO_TERMINATION_CHECK | KwTERMINATING | KwNON_TERMINATING
        | KwNOT_PROJECTION_LIKE
        | KwNON_COVERING
        | KwWARNING_ON_USAGE | KwWARNING_ON_IMPORT
        | KwMEASURE | KwDISPLAY
        | KwREWRITE
        | KwOVERLAPPABLE | KwOVERLAPPING | KwOVERLAPS | KwINCOHERENT
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
  = SymDot          -- ^ @.@
  | SymSemi         -- ^ @;@
  | SymVirtualSemi  -- ^ layout-implied @;@
  | SymBar          -- ^ @|@
  | SymColon        -- ^ @:@
  | SymArrow        -- ^ @->@ or @→@
  | SymEqual        -- ^ @=@
  | SymLambda       -- ^ @\@ or @λ@
  | SymUnderscore   -- ^ @_@
  | SymQuestionMark -- ^ @?@
  | SymAs           -- ^ @@@
  | SymOpenParen    -- ^ @(@
  | SymCloseParen   -- ^ @)@

  | SymEmptyIdiomBracket      -- ^ @(|)@ or @⦇⦈@
  | SymOpenIdiomBracket  Bool -- ^ @(|@ or @⦇@, 'True' if unicode
  | SymCloseIdiomBracket Bool -- ^ @|)@ or @⦈@, 'True' if unicode

  | SymDoubleOpenBrace  Bool  -- ^ @{{@ or @⦃@, 'True' if unicode
  | SymDoubleCloseBrace Bool  -- ^ @{{@ or @⦄@, 'True' if unicode
  | SymOpenBrace              -- ^ @{@
  | SymCloseBrace             -- ^ @}@
  | SymOpenVirtualBrace       -- ^ layout-implied @{@
  | SymCloseVirtualBrace      -- ^ layout-implied @}@
  | SymOpenPragma             -- ^ @{-#@
  | SymClosePragma            -- ^ @#-}@
  | SymEllipsis               -- ^ @...@ or @…@
  | SymDotDot                 -- ^ @..@
  | SymEndComment -- ^ A misplaced end-comment "-}".
  deriving (Eq, Show)

-- | "Tokens" which may appear qualified.
data QualifiableToken
  = QualDo              -- ^ qualified @do@
  | QualEmptyIdiom      -- ^ qualified @(|)@ or @⦇⦈@
  | QualOpenIdiom  Bool -- ^ qualified @(|@ or @⦇@, 'True' if unicode
  deriving (Eq, Show)

-- | A "qualified token", i.e. a sequence of (module) names followed by
-- one of the allowed ('QualifiableToken') keywords/symbols.
data QualifiedToken
  = QualifiedToken
      QualifiableToken     -- ^ The token itself.
      [(Interval, String)] -- ^ Parts for the qualifying identifier, together with their ranges.
      Interval             -- ^ Range of the token being qualified.
  deriving (Eq, Show)

data Token
          -- Keywords
        = TokKeyword Keyword Interval
          -- Identifiers and operators
        | TokId         (Interval, String)
        | TokQId        [(Interval, String)]
                        -- Non-empty namespace. The intervals for
                        -- "A.B.x" correspond to "A.", "B." and "x".
        | TokQual_      QualifiedToken
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

pattern TokQual :: QualifiableToken -> [(Interval, String)] -> Interval -> Token
pattern TokQual clz iss j = TokQual_ (QualifiedToken clz iss j)

{-# COMPLETE TokKeyword, TokId, TokQId, TokQual, TokLiteral, TokSymbol, TokString, TokTeX, TokMarkup, TokComment, TokDummy, TokEOF #-}

instance HasRange QualifiedToken where
  getRange (QualifiedToken _ iss j) = getRange (map fst iss, j)

instance HasRange Token where
  getRange (TokKeyword _ i)    = getRange i
  getRange (TokId (i, _))      = getRange i
  getRange (TokQId iss)        = getRange (map fst iss)
  getRange (TokQual_ q)        = getRange q
  getRange (TokLiteral lit)    = getRange lit
  getRange (TokSymbol _ i)     = getRange i
  getRange (TokString (i, _))  = getRange i
  getRange (TokTeX (i, _))     = getRange i
  getRange (TokMarkup (i, _))  = getRange i
  getRange (TokComment (i, _)) = getRange i
  getRange TokDummy            = noRange
  getRange (TokEOF i)          = getRange i

instance HasRangeWithoutFile Token where
  getRangeWithoutFile = void . getRange
