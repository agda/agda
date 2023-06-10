module Agda.Syntax.Parser.Tokens
    ( Token(..)
    , Keyword(..)
    , layoutKeywords
    , Symbol(..)
    ) where

import Agda.Syntax.Literal (RLiteral)
import Agda.Syntax.Position

import Agda.Utils.Pretty

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
    deriving (Eq, Show, Enum, Bounded)

instance Pretty Keyword where
  pretty = text . \case
    KwLet                  -> "let"
    KwIn                   -> "in"
    KwWhere                -> "where"
    KwData                 -> "data"
    KwCoData               -> "codata"
    KwDo                   -> "do"
    KwPostulate            -> "postulate"
    KwAbstract             -> "abstract"
    KwPrivate              -> "private"
    KwInstance             -> "instance"
    KwInterleaved          -> "interleaved"
    KwMutual               -> "mutual"
    KwOverlap              -> "overlap"
    KwOpen                 -> "open"
    KwImport               -> "import"
    KwModule               -> "module"
    KwPrimitive            -> "primitive"
    KwMacro                -> "macro"
    KwInfix                -> "infix"
    KwInfixL               -> "infixl"
    KwInfixR               -> "infixr"
    KwWith                 -> "with"
    KwRewrite              -> "rewrite"
    KwForall               -> "forall"
    KwRecord               -> "record"
    KwConstructor          -> "constructor"
    KwField                -> "field"
    KwInductive            -> "inductive"
    KwCoInductive          -> "coinductive"
    KwEta                  -> "eta-equality"
    KwNoEta                -> "no-eta-equality"
    KwHiding               -> "hiding"
    KwUsing                -> "using"
    KwRenaming             -> "renaming"
    KwTo                   -> "to"
    KwPublic               -> "public"
    KwOpaque               -> "opaque"
    KwUnfolding            -> "unfolding"
    KwOPTIONS              -> "OPTIONS"
    KwBUILTIN              -> "BUILTIN"
    KwLINE                 -> "LINE"
    KwFOREIGN              -> "FOREIGN"
    KwCOMPILE              -> "COMPILE"
    KwIMPOSSIBLE           -> "IMPOSSIBLE"
    KwSTATIC               -> "STATIC"
    KwINJECTIVE            -> "INJECTIVE"
    KwINLINE               -> "INLINE"
    KwNOINLINE             -> "NOINLINE"
    KwETA                  -> "ETA"
    KwNO_TERMINATION_CHECK -> "NO_TERMINATION_CHECK"
    KwTERMINATING          -> "TERMINATING"
    KwNON_TERMINATING      -> "NON_TERMINATING"
    KwNOT_PROJECTION_LIKE  -> "NOT_PROJECTION_LIKE"
    KwNON_COVERING         -> "NON_COVERING"
    KwWARNING_ON_USAGE     -> "WARNING_ON_USAGE"
    KwWARNING_ON_IMPORT    -> "WARNING_ON_IMPORT"
    KwMEASURE              -> "MEASURE"
    KwDISPLAY              -> "DISPLAY"
    KwREWRITE              -> "REWRITE"
    KwQuote                -> "quote"
    KwQuoteTerm            -> "quoteTerm"
    KwUnquote              -> "unquote"
    KwUnquoteDecl          -> "unquoteDecl"
    KwUnquoteDef           -> "unquoteDef"
    KwSyntax               -> "syntax"
    KwPatternSyn           -> "pattern"
    KwTactic               -> "tactic"
    KwCATCHALL             -> "CATCHALL"
    KwVariable             -> "variable"
    KwNO_POSITIVITY_CHECK  -> "NO_POSITIVITY_CHECK"
    KwPOLARITY             -> "POLARITY"
    KwNO_UNIVERSE_CHECK    -> "NO_UNIVERSE_CHECK"

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
