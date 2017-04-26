{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable    #-}

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
    , parseFile
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
    , parseError, parseErrorAt, parseError'
    , lexError
    )
    where

import Control.Exception (catch)
import Data.Int
import Data.Typeable ( Typeable )

import Control.Monad.State
import Control.Applicative

import Agda.Syntax.Position

import Agda.Utils.Except ( MonadError(catchError, throwError) )
import Agda.Utils.FileName
import qualified Agda.Utils.IO.UTF8 as UTF8
import qualified Agda.Utils.Maybe.Strict as Strict

import Agda.Utils.Pretty

#include "undefined.h"
import Agda.Utils.Impossible

{--------------------------------------------------------------------------
    The parse monad
 --------------------------------------------------------------------------}

-- | The parse monad. Equivalent to @StateT 'ParseState' (Either 'ParseError')@
--   except for the definition of @fail@, which builds a suitable 'ParseError'
--   object.
newtype Parser a = P { unP :: ParseState -> ParseResult a }

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
    , parseFlags    :: ParseFlags            -- ^ currently there are no flags
    }
    deriving Show

{-| To do context sensitive lexing alex provides what is called /start codes/
    in the Alex documentation. It is really an integer representing the state
    of the lexer, so we call it @LexState@ instead.
-}
type LexState = Int

-- | We need to keep track of the context to do layout. The context
--   specifies the indentation (if any) of a layout block. See
--   "Agda.Syntax.Parser.Layout" for more informaton.
data LayoutContext  = NoLayout        -- ^ no layout
                    | Layout Int32    -- ^ layout at specified column
    deriving Show

-- | There aren't any parser flags at the moment.
data ParseFlags = ParseFlags
  { parseKeepComments :: Bool
    -- ^ Should comment tokens be returned by the lexer?
  }
  deriving Show

-- | What you get if parsing fails.
data ParseError =
  -- | Errors that arise at a specific position in the file
  ParseError
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
  } |
  -- | Parse errors that concern a range in a file.
  OverlappingTokensError
  { errRange     :: !(Range' SrcFile)
                    -- ^ The range of the bigger overlapping token
  } |
  -- | Parse errors that concern a whole file.
  InvalidExtensionError
  { errPath      :: !AbsolutePath
                    -- ^ The file which the error concerns.
  , errValidExts :: [String]
  } |
  ReadFileError
  { errPath      :: !AbsolutePath
  , errIOError   :: IOError
  }
  deriving (Typeable)

-- | Warnings for parsing
data ParseWarning =
  -- | Parse errors that concern a range in a file.
  OverlappingTokensWarning
  { warnRange    :: !(Range' SrcFile)
                    -- ^ The range of the bigger overlapping token
  }

-- | The result of parsing something.
data ParseResult a  = ParseOk ParseState a
                    | ParseFailed ParseError

{--------------------------------------------------------------------------
    Instances
 --------------------------------------------------------------------------}

instance Monad Parser where
  return = pure

  P m >>= f = P $ \s -> case m s of
                          ParseFailed e -> ParseFailed e
                          ParseOk s' x  -> unP (f x) s'

  fail msg = P $ \s -> ParseFailed $
                         ParseError  { errSrcFile   = parseSrcFile s
                                     , errPos       = parseLastPos s
                                     , errInput     = parseInp s
                                     , errPrevToken = parsePrevToken s
                                     , errMsg       = msg
                                     }

instance Functor Parser where
  fmap = liftM

instance Applicative Parser where
  pure x = P $ \s -> ParseOk s x
  (<*>)  = ap

instance MonadError ParseError Parser where
  throwError e = P $ \_ -> ParseFailed e

  P m `catchError` h = P $ \s -> case m s of
                                   ParseFailed err -> unP (h err) s
                                   m'              -> m'

instance MonadState ParseState Parser where
  get   = P $ \s -> ParseOk s s
  put s = P $ \_ -> ParseOk s ()

instance Show ParseError where
  show = prettyShow

instance Pretty ParseError where
  pretty ParseError{errPos,errSrcFile,errMsg,errPrevToken,errInput} = vcat
      [ pretty (errPos { srcFile = errSrcFile }) <> colon <+>
        text errMsg
      , text $ errPrevToken ++ "<ERROR>"
      , text $ take 30 errInput ++ "..."
      ]
  pretty OverlappingTokensError{errRange} = vcat
      [ pretty errRange <> colon <+>
        text "Multi-line comment spans one or more literate text blocks."
      ]
  pretty InvalidExtensionError{errPath,errValidExts} = vcat
      [ pretty errPath <> colon <+>
        text "Unsupported extension."
      , text "Supported extensions are:" <+> prettyList_ errValidExts
      ]
  pretty ReadFileError{errPath,errIOError} = vcat
      [ text "Cannot read file" <+> pretty errPath
        -- TODO: `show` should be replaced by `displayException` once we
        -- cease to support versions of GHC under 7.10.
      , text "Error:" <+> text (show errIOError)
      ]

instance HasRange ParseError where
  getRange ParseError{errSrcFile,errPos=p} = posToRange' errSrcFile p p
  getRange OverlappingTokensError{errRange} = errRange
  getRange InvalidExtensionError{errPath} = posToRange p p
    where p = startPos (Just errPath)
  getRange ReadFileError{errPath} = posToRange p p
    where p = startPos (Just errPath)

instance Show ParseWarning where
  show = prettyShow

instance Pretty ParseWarning where
  pretty OverlappingTokensWarning{warnRange} = vcat
      [ pretty warnRange <> colon <+>
        text "Multi-line comment spans one or more literate text blocks."
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

-- | The most general way of parsing a file. The "Agda.Syntax.Parser" will define
--   more specialised functions that supply the 'ParseFlags' and the
--   'LexState'.
--
--   Note that Agda source files always use the UTF-8 character
--   encoding.
parseFile :: ParseFlags -> [LexState] -> Parser a -> AbsolutePath
          -> IO (ParseResult a)
parseFile flags st p file =
    do  res <- (Right <$> (UTF8.readTextFile (filePath file))) `catch`
          (return . Left . ReadFileError file)
        case res of
          Left  error -> return$ ParseFailed error
          Right input -> return$ parseFromSrc flags st p (Strict.Just file) input

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
getLastPos = get >>= return . parseLastPos

-- | The parse interval is between the last position and the current position.
getParseInterval :: Parser Interval
getParseInterval = do
  s <- get
  return $ posToInterval (parseSrcFile s) (parseLastPos s) (parsePos s)

getLexState :: Parser [LexState]
getLexState = parseLexState <$> get

setLexState :: [LexState] -> Parser ()
setLexState ls =
    do  s <- get
        put $ s { parseLexState = ls }

pushLexState :: LexState -> Parser ()
pushLexState l = do s <- getLexState
                    setLexState (l:s)

popLexState :: Parser ()
popLexState = do _:ls <- getLexState
                 setLexState ls

getParseFlags :: Parser ParseFlags
getParseFlags = parseFlags <$> get


-- | @parseError = fail@
parseError :: String -> Parser a
parseError = fail


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


-- | For lexical errors we want to report the current position as the site of
--   the error, whereas for parse errors the previous position is the one
--   we're interested in (since this will be the position of the token we just
--   lexed). This function does 'parseErrorAt' the current position.
lexError :: String -> Parser a
lexError msg =
    do  p <- parsePos <$> get
        parseErrorAt p msg

{--------------------------------------------------------------------------
    Layout
 --------------------------------------------------------------------------}

getContext :: Parser [LayoutContext]
getContext = parseLayout <$> get

setContext :: [LayoutContext] -> Parser ()
setContext ctx =
    do  s <- get
        put $ s { parseLayout = ctx }

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
