
module Agda.Syntax.Parser.Monad
    ( -- * The parser monad
      Parser
    , ParseResult(..)
    , ParseState(..)
    , ParseError(..), ParseWarning(..)
    , LexState
    , OpenBracket(..)
    , LayoutBlock(..), LayoutContext, LayoutStatus(..)
    , Column
    , ParseFlags (..)
      -- * Running the parser
    , initState
    , defaultParseFlags
    , parse
    , parsePosString
    , parseFromSrc
      -- * Manipulating the state
    , setParsePos, setLastPos, getParseInterval
    , setPrevToken
    , getParseFlags
    , getLexState, pushLexState, popLexState
      -- ** Layout
    , topBlock, popBlock, pushBlock
    , getContext, setContext, modifyContext
    , resetLayoutStatus
      -- ** Brackets
    , openBracket, closeBracket
      -- ** Errors
    , parseWarning, parseWarningName
    , parseError, parseErrorAt, parseError', parseErrorRange
    , lexError
    )
    where

import Prelude hiding ( null )

import Control.DeepSeq
import Control.Exception ( displayException )
import Control.Monad.Except
import Control.Monad.State
import Control.Monad

import Data.Maybe ( listToMaybe, fromMaybe )
import Data.Word  ( Word32 )
import Data.List  ( uncons )

import Agda.Interaction.Options.Warnings

import Agda.Syntax.Common.Pretty
import Agda.Syntax.Concrete.Attribute
import Agda.Syntax.Position
import Agda.Syntax.Parser.Tokens ( Keyword( KwMutual ), Token(..), Symbol(..), QualifiableToken (QualOpenIdiom) )

import Agda.TypeChecking.Positivity.Occurrence ( pattern Mixed )

import Agda.Utils.Function ( applyUnless )
import Agda.Utils.Functor  ( (<&>) )
import Agda.Utils.IO   ( showIOException )
import Agda.Utils.List ( tailWithDefault )
import Agda.Utils.Maybe.Strict qualified as Strict
import Agda.Utils.Null

import Agda.Utils.Impossible

{--------------------------------------------------------------------------
    The parse monad
 --------------------------------------------------------------------------}

-- | The parse monad.
newtype Parser a = P { _runP :: StateT ParseState (Either ParseError) a }
  deriving (Functor, Applicative, Monad, MonadState ParseState, MonadError ParseError)

-- | The parser state. Contains everything the parser and the lexer could ever
--   need.
data ParseState = PState
    { parseSrcFile    :: !SrcFile
    , parsePos        :: !PositionWithoutFile  -- ^ position at current input location
    , parseLastPos    :: !PositionWithoutFile  -- ^ position of last token
    , parseInp        :: String                -- ^ the current input
    , parsePrevChar   :: !Char                 -- ^ the character before the input
    , parsePrevToken  :: String                -- ^ the previous token
    , parseLayout     :: LayoutContext         -- ^ the stack of layout blocks
    , parseLayStatus  :: LayoutStatus          -- ^ the status of the coming layout block
    , parseLayKw      :: Keyword               -- ^ the keyword for the coming layout block
    , parseLexState   :: [LexState]            -- ^ the state of the lexer
                                             --   (states can be nested so we need a stack)
    , parseFlags      :: ParseFlags            -- ^ parametrization of the parser
    , parseWarnings   :: ![ParseWarning]       -- ^ In reverse order.
    , parseBrackets   :: [OpenBracket]         -- ^ stack of open unicode/ASCII brackets
    , parseAttributes :: !Attributes         -- ^ Every encountered attribute.
    }
    deriving Show

{-| For context sensitive lexing alex provides what is called /start codes/
    in the Alex documentation.  It is really an integer representing the state
    of the lexer, so we call it @LexState@ instead.
-}
type LexState = Int

-- | The stack of layout blocks.
--
--   When we encounter a layout keyword, we push a 'Tentative' block
--   with 'noColumn'.  This is replaced by aproper column once we
--   reach the next token.
type LayoutContext = [LayoutBlock]

-- | We need to keep track of the context to do layout. The context
--   specifies the indentation columns of the open layout blocks. See
--   "Agda.Syntax.Parser.Layout" for more informaton.
data LayoutBlock
  = Layout Keyword LayoutStatus Column
      -- ^ Layout at specified 'Column', introduced by 'Keyword'.
    deriving Show

-- | A (layout) column.
type Column = Word32

-- | Status of a layout column (see #1145).
--   A layout column is 'Tentative' until we encounter a new line.
--   This allows stacking of layout keywords.
--
--   Inside a @LayoutContext@ the sequence of 'Confirmed' columns
--   needs to be strictly increasing.
--   'Tentative columns between 'Confirmed' columns need to be
--   strictly increasing as well.
data LayoutStatus
  = Tentative  -- ^ The token defining the layout column was on the same line
               --   as the layout keyword and we have not seen a new line yet.
  | Confirmed  -- ^ We have seen a new line since the layout keyword
               --   and the layout column has not been superseded by
               --   a smaller column.
    deriving (Eq, Show)

-- | Information about an opening unicode-able bracket necessary for
-- correctly parsing its closing delimiter.
data OpenBracket
  -- | An opening idiom bracket.
  = OpenIdiomBracket
    { openBracketUnicode  :: Bool     -- ^ 'True' if the user wrote @⦇@.
    , openBracketInterval :: Interval -- ^ Position of the opening bracket.
    }
  -- | An opening double brace.
  | OpenDoubleBrace
    { openBracketUnicode  :: Bool     -- ^ 'True' if the user wrote @⦃@.
    , openBracketInterval :: Interval -- ^ Position of the opening bracket.
    }
  deriving (Eq, Show)

instance NFData OpenBracket where
  rnf (OpenIdiomBracket x _) = rnf x
  rnf (OpenDoubleBrace  x _) = rnf x

-- | Parser flags.
data ParseFlags = ParseFlags
  { parseKeepComments :: Bool
    -- ^ Should comment tokens be returned by the lexer?
  }
  deriving Show

-- | Parse errors: what you get if parsing fails.
data ParseError

  -- | Errors that arise at a specific position in the file
  = ParseError
    { errPos       :: !Position
                      -- ^ Where the error occurred.
    , errInput     :: String
                      -- ^ The remaining input.
    , errPrevToken :: String
                      -- ^ The previous token.
    , errMsg       :: String
                      -- ^ Hopefully an explanation of what happened.
    }

  -- | Parse errors that concern a range in a file.
  | OverlappingTokensError
    { errRange     :: !Range
                      -- ^ The range of the bigger overlapping token
    }

  -- | Parse errors that concern a whole file.
  | InvalidExtensionError
    { errPath      :: !RangeFile
                      -- ^ The file which the error concerns.
    , errValidExts :: [String]
    }
  | ReadFileError
    { errPath      :: !RangeFile
    , errIOError   :: IOError
    }
  deriving Show

instance KillRange ParseError where
  killRange = \case
    ParseError _ inp tok msg     -> ParseError empty inp tok msg
    OverlappingTokensError _     -> OverlappingTokensError empty
    InvalidExtensionError _ exts -> InvalidExtensionError empty exts
    ReadFileError _ err          -> ReadFileError empty err

instance NFData ParseError where
  rnf = \case
    ParseError _r inp tok msg     -> rnf inp `seq` rnf tok `seq` rnf msg
    OverlappingTokensError _r     -> ()
    InvalidExtensionError _r exts -> rnf exts
    ReadFileError _r _err         -> ()

-- | Warnings for parsing.
data ParseWarning
  -- | Parse errors that concern a range in a file.
  = OverlappingTokensWarning
    { warnRange :: !(Range' SrcFile)
        -- ^ The range of the bigger overlapping token.
    }
  | MisplacedAttributes Range String
      -- ^ The 'String' is the error message.
  | UnknownPolarity Range String
      -- ^ Unknown polarity, ignored.
  | UnknownAttribute Range String
      -- ^ Unknown attribute, ignored.
      --   The 'Range' includes the "@", the 'String' not.
  | UnsupportedAttribute Range !(Maybe String)
      -- ^ Unsupported attribute.
  | MultipleAttributes Range !(Maybe String)
      -- ^ Multiple attributes.
  | MismatchedBrackets Range OpenBracket
      -- ^ The closing bracket (at the 'Range') was closed with a
      -- unicode-ness that doesn't match that of the 'OpenBracket'.
  deriving Show

instance NFData ParseWarning where
  rnf (OverlappingTokensWarning _) = ()
  rnf (MisplacedAttributes _ s)    = rnf s
  rnf (UnknownPolarity _ s)        = rnf s
  rnf (UnknownAttribute _ s)       = rnf s
  rnf (UnsupportedAttribute _ s)   = rnf s
  rnf (MultipleAttributes _ s)     = rnf s
  rnf (MismatchedBrackets _ s)     = rnf s

parseWarningName :: ParseWarning -> WarningName
parseWarningName = \case
  OverlappingTokensWarning{} -> OverlappingTokensWarning_
  MisplacedAttributes{}      -> MisplacedAttributes_
  UnknownPolarity{}          -> UnknownPolarity_
  UnknownAttribute{}         -> UnknownAttribute_
  UnsupportedAttribute{}     -> UnsupportedAttribute_
  MultipleAttributes{}       -> MultipleAttributes_
  MismatchedBrackets{}       -> MismatchedBrackets_

-- | The result of parsing something.
data ParseResult a
  = ParseOk ParseState a
  | ParseFailed ParseError
  deriving Show

-- | Old interface to parser.
unP :: Parser a -> ParseState -> ParseResult a
unP (P m) s = case runStateT m s of
  Left err     -> ParseFailed err
  Right (a, s) -> ParseOk s a

-- | Throw a parse error at the current position.
parseError :: String -> Parser a
parseError msg = do
  s <- get
  throwError $ ParseError
    { errPos       = parseLastPos s <&> const (parseSrcFile s)
    , errInput     = parseInp s
    , errPrevToken = parsePrevToken s
    , errMsg       = msg
    }

-- | Records a warning.

parseWarning :: ParseWarning -> Parser ()
parseWarning w =
  modify' $ \s -> s { parseWarnings = w : parseWarnings s }

{--------------------------------------------------------------------------
    Instances
 --------------------------------------------------------------------------}

instance Pretty ParseError where
  pretty ParseError{ errPos, errMsg, errPrevToken, errInput } = vcat
      [ applyUnless (null errPos) ((pretty errPos <> colon) <+>) "error: [ParseError]"
      , if not $ null errMsg then text errMsg else sep
          -- Happy errors have no message, so we print the context instead
          [ text $ errPrevToken ++ "<ERROR>"
          , text $ take 30 errInput ++ "..."
          ]
      ]
  pretty OverlappingTokensError{errRange} = vcat
      [ applyUnless (null errRange) ((pretty errRange <> colon) <+>) "error: [OverlappingTokensError]"
      , "Multi-line comment spans one or more literate text blocks."
      ]
  pretty InvalidExtensionError{errPath,errValidExts} = vcat
      [ applyUnless (null errPath) ((pretty errPath <> colon) <+>) "error: [InvalidExtensionError]"
      , "Unsupported extension."
      , "Supported extensions are:" <+> prettyList_ errValidExts
      ]
  pretty ReadFileError{errPath,errIOError} = vcat $ concat
      [ [ "Cannot read file" <+> pretty errPath | not (null errPath) ]
      , [ "Error:" <+> text (showIOException errIOError) ]
      ]

instance HasRange ParseError where
  getRange err = case err of
      ParseError{ errPos = p }             -> posToRange p p
      OverlappingTokensError{ errRange }   -> errRange
      InvalidExtensionError{}              -> errPathRange
      ReadFileError{}                      -> errPathRange
    where
    errPathRange = posToRange p p
      where p = startPos $ Just $ errPath err

-- | Does not include printing of the range.
--
instance Pretty ParseWarning where
  pretty = \case

    OverlappingTokensWarning _r ->
      "Multi-line comment spans one or more literate text blocks."

    MisplacedAttributes _r s -> text s

    UnknownPolarity _r s ->
      "Replacing unknown polarity" <+> text s <+> "by" <+> pretty Mixed

    UnknownAttribute _r s ->
      "Ignoring unknown attribute:" <+> ("@" <> text s)

    UnsupportedAttribute _r ms -> hsep
      [ case ms of
          Nothing -> "Attributes"
          Just s  -> text s <+> "attributes"
      , "are not supported here."
      ]

    MismatchedBrackets _r brk ->
      let
        (nm, op, cl) = case brk of
          OpenIdiomBracket True  _ -> ("Idiom brackets", "\x2987", "\x2988")
          OpenIdiomBracket False _ -> ("Idiom brackets", "(|",     "|)")
          OpenDoubleBrace  True  _ -> ("Double braces",  "\x2983", "\x2984")
          OpenDoubleBrace  False _ -> ("Double braces",  "{{",     "}}")
      in nm <> " opened with `" <> op <> "` must be closed with `" <> cl <> "`."

    MultipleAttributes _r ms -> hsep
      [ "Multiple", pretty ms, "attributes (ignored)." ]


instance HasRange ParseWarning where
  getRange OverlappingTokensWarning{warnRange} = warnRange
  getRange (MisplacedAttributes r _)           = r
  getRange (UnknownPolarity r _)               = r
  getRange (UnknownAttribute r _)              = r
  getRange (UnsupportedAttribute r _)          = r
  getRange (MultipleAttributes r _)            = r
  getRange (MismatchedBrackets r _)            = r

{--------------------------------------------------------------------------
    Running the parser
 --------------------------------------------------------------------------}

initStatePos :: Position -> ParseFlags -> String -> [LexState] -> ParseState
initStatePos pos flags inp st =
        PState  { parseSrcFile      = srcFile pos
                , parsePos          = pos'
                , parseLastPos      = pos'
                , parseInp          = inp
                , parsePrevChar     = '\n'
                , parsePrevToken    = ""
                , parseLexState     = st
                , parseLayout       = []        -- the first block will be from the top-level layout
                , parseLayStatus    = Confirmed -- for the to-be-determined column of the top-level layout
                , parseLayKw        = KwMutual  -- Layout keyword for the top-level layout.
                                                -- Does not mean that the top-level block is a mutual block.
                                                -- Just for better errors on stray @constructor@ decls.
                , parseFlags        = flags
                , parseWarnings     = []
                , parseAttributes   = []
                , parseBrackets     = []
                }
  where
  pos' = pos { srcFile = () }

-- | Constructs the initial state of the parser. The string argument
--   is the input string, the file path is only there because it's part
--   of a position.
initState ::
  Maybe RangeFile -> ParseFlags -> String -> [LexState] -> ParseState
initState file = initStatePos (startPos file)

-- | The default flags.
defaultParseFlags :: ParseFlags
defaultParseFlags = ParseFlags { parseKeepComments = False }

-- | The most general way of parsing a string. The "Agda.Syntax.Parser" will define
--   more specialised functions that supply the 'ParseFlags' and the
--   'LexState'.
parse :: ParseFlags -> [LexState] -> Parser a -> String -> ParseResult a
parse flags st p input = parseFromSrc flags st p Strict.Nothing input

-- | The even more general way of parsing a string.
parsePosString :: Position -> ParseFlags -> [LexState] -> Parser a -> String ->
                  ParseResult a
parsePosString pos flags st p input = unP p (initStatePos pos flags input st)

-- | Calls 'parsePosString' with 'Position' extracted from the Range.
parseRangeString :: Range -> ParseFlags -> [LexState] -> Parser a -> String ->
                    ParseResult a
parseRangeString = parsePosString . fromMaybe (startPos Nothing) . rStart

-- | Parses a string as if it were the contents of the given file
--   Useful for integrating preprocessors.
parseFromSrc :: ParseFlags -> [LexState] -> Parser a -> SrcFile -> String
              -> ParseResult a
parseFromSrc flags st p src input = unP p (initState (Strict.toLazy src) flags input st)


{--------------------------------------------------------------------------
    Manipulating the state
 --------------------------------------------------------------------------}

setParsePos :: PositionWithoutFile -> Parser ()
setParsePos p = modify $ \s -> s { parsePos = p }

setLastPos :: PositionWithoutFile -> Parser ()
setLastPos p = modify $ \s -> s { parseLastPos = p }

setPrevToken :: String -> Parser ()
setPrevToken t = modify $ \s -> s { parsePrevToken = t }

getLastPos :: Parser PositionWithoutFile
getLastPos = gets parseLastPos

-- | The parse interval is between the last position and the current position.
getParseInterval :: Parser Interval
getParseInterval = do
  s <- get
  return $ posToInterval (parseSrcFile s) (parseLastPos s) (parsePos s)

getLexState :: Parser [LexState]
getLexState = gets parseLexState

-- UNUSED Liang-Ting Chen 2019-07-16
--setLexState :: [LexState] -> Parser ()
--setLexState ls = modify $ \ s -> s { parseLexState = ls }

modifyLexState :: ([LexState] -> [LexState]) -> Parser ()
modifyLexState f = modify $ \ s -> s { parseLexState = f (parseLexState s) }

pushLexState :: LexState -> Parser ()
pushLexState l = modifyLexState (l:)

popLexState :: Parser ()
popLexState = modifyLexState $ tailWithDefault __IMPOSSIBLE__

getParseFlags :: Parser ParseFlags
getParseFlags = gets parseFlags


-- | Fake a parse error at the specified position. Used, for instance, when
--   lexing nested comments, which when failing will always fail at the end
--   of the file. A more informative position is the beginning of the failing
--   comment.
parseErrorAt :: PositionWithoutFile -> String -> Parser a
parseErrorAt p msg =
    do  setLastPos p
        parseError msg

-- | Use 'parseErrorAt' or 'parseError' as appropriate.
parseError' :: Maybe PositionWithoutFile -> String -> Parser a
parseError' = maybe parseError parseErrorAt

-- | Report a parse error at the beginning of the given 'Range'.
parseErrorRange :: HasRange r => r -> String -> Parser a
parseErrorRange = parseError' . rStart' . getRange


-- | For lexical errors we want to report the current position as the site of
--   the error, whereas for parse errors the previous position is the one
--   we're interested in (since this will be the position of the token we just
--   lexed). This function does 'parseErrorAt' the current position.
lexError :: String -> Parser a
lexError msg =
    do  p <- gets parsePos
        parseErrorAt p msg

{--------------------------------------------------------------------------
    Layout
 --------------------------------------------------------------------------}

getContext :: MonadState ParseState m => m LayoutContext
getContext = gets parseLayout

setContext :: LayoutContext -> Parser ()
setContext = modifyContext . const

modifyContext :: (LayoutContext -> LayoutContext) -> Parser ()
modifyContext f = modify $ \ s -> s { parseLayout = f (parseLayout s) }

-- | Return the current layout block.
topBlock :: Parser (Maybe LayoutBlock)
topBlock = listToMaybe <$> getContext

popBlock :: Parser ()
popBlock =
    do  ctx <- getContext
        case ctx of
            []      -> parseError "There is no layout block to close at this point."
            _:ctx   -> setContext ctx

pushBlock :: LayoutBlock -> Parser ()
pushBlock l = modifyContext (l :)

-- | When we see a layout keyword, by default we expect a 'Tentative' block.
resetLayoutStatus :: Parser ()
resetLayoutStatus = modify $ \ s -> s { parseLayStatus = Tentative }

------------------------------------------------------------------------
-- * Brackets

-- | Push the 'OpenBracket' state corresponding to an opening token.
openBracket :: Token -> Parser Range
openBracket tok =
  case tok of
    TokSymbol (SymOpenIdiomBracket u)   r -> push r $ OpenIdiomBracket u
    TokSymbol (SymDoubleOpenBrace  u)   r -> push r $ OpenDoubleBrace  u
    TokQual   (QualOpenIdiom       u) _ r -> push r $ OpenIdiomBracket u

    -- These are the only tokens we call this for.
    _ -> __IMPOSSIBLE__
  where push rng k = getRange rng <$ modify \s -> s { parseBrackets = k rng:parseBrackets s}

-- | Pop an 'OpenBracket' from the parser state, and generate the
-- 'MismatchedBrackets' warning if the given 'Token' does not match what
-- was expected.
closeBracket :: Token -> Parser Range
closeBracket (TokSymbol sym ivl) = do
  let
    rng          = getRange ivl
    match a b xs = rng <$ do
      unless (openBracketUnicode a == b) $ parseWarning $ MismatchedBrackets rng a
      modify \s -> s { parseBrackets = xs }

  -- Since Happy won't call the action if the rule doesn't match, and we
  -- call this function from the *parser*, this function is guaranteed
  -- to only run if the parser is expecting a closing delimiter of the
  -- right type.
  gets parseBrackets >>= \case
    open@OpenIdiomBracket{}:xs
      | SymCloseIdiomBracket uC <- sym -> match open uC xs
      | otherwise                      -> __IMPOSSIBLE__
    open@OpenDoubleBrace{}:xs
      | SymDoubleCloseBrace  uC <- sym -> match open uC xs
      | otherwise                      -> __IMPOSSIBLE__
    [] -> __IMPOSSIBLE__

-- Only symbols can be closing delimiters.
closeBracket _ = __IMPOSSIBLE__
