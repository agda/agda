{-# LANGUAGE DeriveDataTypeable    #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Agda.Syntax.Parser.Monad
    ( -- * The parser monad
      Parser
    , ParseResult(..)
    , ParseState(..)
    , ParseError(..), ParseWarning(..)
    , LexState
    , LayoutContext(..)
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
    , topContext, popContext, pushContext
    , pushCurrentContext
      -- ** Errors
    , parseWarningName
    , parseError, parseErrorAt, parseError', parseErrorRange
    , lexError
    )
    where

import Control.Exception (catch, displayException)
import Data.Int

import Data.Data (Data)
import qualified Data.Text.Lazy as T

import Control.Monad.State
import Control.Monad.Except

import Agda.Interaction.Options.Warnings

import Agda.Syntax.Position

import Agda.Utils.Except ( MonadError(catchError, throwError) )
import Agda.Utils.FileName
import Agda.Utils.List ( tailWithDefault )
import qualified Agda.Utils.IO.UTF8 as UTF8
import qualified Agda.Utils.Maybe.Strict as Strict

import Agda.Utils.Pretty

import Agda.Utils.Impossible

{--------------------------------------------------------------------------
    The parse monad
 --------------------------------------------------------------------------}

-- | The parse monad.
newtype Parser a = P { runP :: StateT ParseState (Either ParseError) a }
  deriving (Functor, Applicative, Monad, MonadState ParseState, MonadError ParseError)

-- | The parser state. Contains everything the parser and the lexer could ever
--   need.
data ParseState = PState
    { parseSrcFile  :: !SrcFile
    , parsePos      :: !PositionWithoutFile  -- ^ position at current input location
    , parseLastPos  :: !PositionWithoutFile  -- ^ position of last token
    , parseInp      :: String                -- ^ the current input
    , parsePrevChar :: !Char                 -- ^ the character before the input
    , parsePrevToken:: String                -- ^ the previous token
    , parseLayout   :: [LayoutContext]       -- ^ the stack of layout contexts
    , parseLexState :: [LexState]            -- ^ the state of the lexer
                                             --   (states can be nested so we need a stack)
    , parseFlags    :: ParseFlags            -- ^ parametrization of the parser
    }
    deriving Show

{-| For context sensitive lexing alex provides what is called /start codes/
    in the Alex documentation.  It is really an integer representing the state
    of the lexer, so we call it @LexState@ instead.
-}
type LexState = Int

-- | We need to keep track of the context to do layout. The context
--   specifies the indentation (if any) of a layout block. See
--   "Agda.Syntax.Parser.Layout" for more informaton.
data LayoutContext  = NoLayout        -- ^ no layout
                    | Layout Int32    -- ^ layout at specified column
    deriving Show

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
    { errSrcFile   :: !SrcFile
                      -- ^ The file in which the error occurred.
    , errPos       :: !PositionWithoutFile
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
    { errRange     :: !(Range' SrcFile)
                      -- ^ The range of the bigger overlapping token
    }

  -- | Parse errors that concern a whole file.
  | InvalidExtensionError
    { errPath      :: !AbsolutePath
                      -- ^ The file which the error concerns.
    , errValidExts :: [String]
    }
  | ReadFileError
    { errPath      :: !AbsolutePath
    , errIOError   :: IOError
    }

-- | Warnings for parsing.
data ParseWarning
  -- | Parse errors that concern a range in a file.
  = OverlappingTokensWarning
    { warnRange    :: !(Range' SrcFile)
                      -- ^ The range of the bigger overlapping token
    }
  deriving Data

parseWarningName :: ParseWarning -> WarningName
parseWarningName = \case
  OverlappingTokensWarning{} -> OverlappingTokensWarning_

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
    { errSrcFile   = parseSrcFile s
    , errPos       = parseLastPos s
    , errInput     = parseInp s
    , errPrevToken = parsePrevToken s
    , errMsg       = msg
    }

{--------------------------------------------------------------------------
    Instances
 --------------------------------------------------------------------------}

instance Show ParseError where
  show = prettyShow

instance Pretty ParseError where
  pretty ParseError{errPos,errSrcFile,errMsg,errPrevToken,errInput} = vcat
      [ (pretty (errPos { srcFile = errSrcFile }) <> colon) <+>
        text errMsg
      , text $ errPrevToken ++ "<ERROR>"
      , text $ take 30 errInput ++ "..."
      ]
  pretty OverlappingTokensError{errRange} = vcat
      [ (pretty errRange <> colon) <+>
        "Multi-line comment spans one or more literate text blocks."
      ]
  pretty InvalidExtensionError{errPath,errValidExts} = vcat
      [ (pretty errPath <> colon) <+>
        "Unsupported extension."
      , "Supported extensions are:" <+> prettyList_ errValidExts
      ]
  pretty ReadFileError{errPath,errIOError} = vcat
      [ "Cannot read file" <+> pretty errPath
      , "Error:" <+> text (displayException errIOError)
      ]

instance HasRange ParseError where
  getRange err = case err of
      ParseError{ errSrcFile, errPos = p } -> posToRange' errSrcFile p p
      OverlappingTokensError{ errRange }   -> errRange
      InvalidExtensionError{}              -> errPathRange
      ReadFileError{}                      -> errPathRange
    where
    errPathRange = posToRange p p
      where p = startPos $ Just $ errPath err

instance Show ParseWarning where
  show = prettyShow

instance Pretty ParseWarning where
  pretty OverlappingTokensWarning{warnRange} = vcat
      [ (pretty warnRange <> colon) <+>
        "Multi-line comment spans one or more literate text blocks."
      ]
instance HasRange ParseWarning where
  getRange OverlappingTokensWarning{warnRange} = warnRange

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
                , parseLayout       = [NoLayout]
                , parseFlags        = flags
                }
  where
  pos' = pos { srcFile = () }

-- | Constructs the initial state of the parser. The string argument
--   is the input string, the file path is only there because it's part
--   of a position.
initState :: Maybe AbsolutePath -> ParseFlags -> String -> [LexState]
          -> ParseState
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
getLexState = parseLexState <$> get

setLexState :: [LexState] -> Parser ()
setLexState ls = modify $ \ s -> s { parseLexState = ls }

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

getContext :: Parser [LayoutContext]
getContext = gets parseLayout

setContext :: [LayoutContext] -> Parser ()
setContext ctx = modify $ \ s -> s { parseLayout = ctx }

-- | Return the current layout context.
topContext :: Parser LayoutContext
topContext =
    do  ctx <- getContext
        case ctx of
            []  -> parseError "No layout context in scope"
            l:_ -> return l

popContext :: Parser ()
popContext =
    do  ctx <- getContext
        case ctx of
            []      -> parseError "There is no layout block to close at this point."
            _:ctx   -> setContext ctx

pushContext :: LayoutContext -> Parser ()
pushContext l =
    do  ctx <- getContext
        setContext (l : ctx)

-- | Should only be used at the beginning of a file. When we start parsing
--   we should be in layout mode. Instead of forcing zero indentation we use
--   the indentation of the first token.
pushCurrentContext :: Parser ()
pushCurrentContext =
    do  p <- getLastPos
        pushContext (Layout (posCol p))
