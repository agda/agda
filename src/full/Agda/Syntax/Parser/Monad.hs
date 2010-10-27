{-# LANGUAGE MultiParamTypeClasses, DeriveDataTypeable #-}
module Agda.Syntax.Parser.Monad
    ( -- * The parser monad
      Parser
    , ParseResult(..)
    , ParseState(..)
    , ParseError(..)
    , LexState
    , LayoutContext(..)
    , ParseFlags (..)
      -- * Running the parser
    , initState
    , defaultParseFlags
    , parse
    , parsePosString
    , parseFile
      -- * Manipulating the state
    , setParsePos, setLastPos, getParseInterval
    , setPrevToken
    , getParseFlags
    , getLexState, pushLexState, popLexState
      -- ** Layout
    , topContext, popContext, pushContext
    , pushCurrentContext
      -- ** Errors
    , parseError, parseErrorAt
    , lexError
    )
    where

import Control.Exception
import Data.Char
import Data.Int
import Data.Typeable

import Control.Monad.State
import Control.Monad.Error
import Control.Applicative

import Agda.Syntax.Position

import Agda.Utils.FileName
import qualified Agda.Utils.IO.UTF8 as UTF8
import Agda.Utils.Monad

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
    { parsePos	    :: !Position	-- ^ position at current input location
    , parseLastPos  :: !Position	-- ^ position of last token
    , parseInp	    :: String		-- ^ the current input
    , parsePrevChar :: !Char		-- ^ the character before the input
    , parsePrevToken:: String		-- ^ the previous token
    , parseLayout   :: [LayoutContext]	-- ^ the stack of layout contexts
    , parseLexState :: [LexState]	-- ^ the state of the lexer
					--   (states can be nested so we need a stack)
    , parseFlags    :: ParseFlags	-- ^ currently there are no flags
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
data LayoutContext  = NoLayout	      -- ^ no layout
		    | Layout Int32    -- ^ layout at specified column
    deriving Show

-- | There aren't any parser flags at the moment.
data ParseFlags	= ParseFlags
  { parseKeepComments :: Bool
    -- ^ Should comment tokens be returned by the lexer?
  }
  deriving Show

-- | What you get if parsing fails.
data ParseError	= ParseError
		    { errPos	    :: Position	-- ^ where the error occured
		    , errInput	    :: String	-- ^ the remaining input
		    , errPrevToken  :: String	-- ^ the previous token
		    , errMsg	    :: String	-- ^ hopefully an explanation
						--   of what happened
		    }
    deriving (Typeable)

instance Exception ParseError

-- | The result of parsing something.
data ParseResult a  = ParseOk ParseState a
		    | ParseFailed ParseError

{--------------------------------------------------------------------------
    Instances
 --------------------------------------------------------------------------}

instance Monad Parser where
    return x	= P $ \s -> ParseOk s x
    P m >>= f	= P $ \s -> case m s of
				ParseFailed e	-> ParseFailed e
				ParseOk s' x	-> unP (f x) s'
    fail msg	= P $ \s -> ParseFailed $
				ParseError  { errPos	    = parseLastPos s
					    , errInput	    = parseInp s
					    , errPrevToken  = parsePrevToken s
					    , errMsg	    = msg
					    }

instance Functor Parser where
    fmap = liftM

instance Applicative Parser where
    pure = return
    (<*>) = ap

instance MonadError ParseError Parser where
    throwError e	= P $ \_ -> ParseFailed e
    P m `catchError` h	= P $ \s -> case m s of
					ParseFailed err	-> unP (h err) s
					m'		-> m'

instance MonadState ParseState Parser where
    get	    = P $ \s -> ParseOk s s
    put s   = P $ \_ -> ParseOk s ()

instance Show ParseError where
    show err =
	unlines
	    [ pos ++ ": " ++ errMsg err
	    --, replicate (length pos + 2) ' ' ++ "on '" ++ errPrevToken err ++ "'"
            , errPrevToken err ++ "<ERROR>\n" ++ take 30 (errInput err) ++ "..."
	    ]
	where
	    pos = show (errPos err)

-- 	    showInp ""  = "at end of file"
-- 	    showInp t   = "on input " ++ elide 5 t
--
-- 	    elide 3 s
-- 		| length (take 4 s) < 4 = s
-- 		| otherwise		    = "..."
-- 	    elide n (c:s)		    = c : elide (n - 1) s
-- 	    elide _ ""		    = ""

instance HasRange ParseError where
    getRange err = posToRange (errPos err) (errPos err)

{--------------------------------------------------------------------------
    Running the parser
 --------------------------------------------------------------------------}

initStatePos :: Position -> ParseFlags -> String -> [LexState] -> ParseState
initStatePos pos flags inp st =
	PState  { parsePos	    = pos
		, parseLastPos	    = pos
		, parseInp	    = inp
		, parsePrevChar	    = '\n'
		, parsePrevToken    = ""
		, parseLexState	    = st
		, parseLayout	    = [NoLayout]
		, parseFlags	    = flags
		}

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
parse flags st p input = unP p (initState Nothing flags input st)

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
    do	input <- liftIO $ UTF8.readTextFile $ filePath file
	return $ unP p (initState (Just file) flags input st)

{--------------------------------------------------------------------------
    Manipulating the state
 --------------------------------------------------------------------------}

setParsePos :: Position -> Parser ()
setParsePos p = modify $ \s -> s { parsePos = p }

setLastPos :: Position -> Parser ()
setLastPos p = modify $ \s -> s { parseLastPos = p }

setPrevToken :: String -> Parser ()
setPrevToken t = modify $ \s -> s { parsePrevToken = t }

getLastPos :: Parser Position
getLastPos = get >>= return . parseLastPos

-- | The parse interval is between the last position and the current position.
getParseInterval :: Parser Interval
getParseInterval =
    do	s <- get
	return $ Interval (parseLastPos s) (parsePos s)

getLexState :: Parser [LexState]
getLexState = parseLexState <$> get

setLexState :: [LexState] -> Parser ()
setLexState ls =
    do	s <- get
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
parseErrorAt :: Position -> String -> Parser a
parseErrorAt p msg =
    do	setLastPos p
	parseError msg


-- | For lexical errors we want to report the current position as the site of
--   the error, whereas for parse errors the previous position is the one
--   we're interested in (since this will be the position of the token we just
--   lexed). This function does 'parseErrorAt' the current position.
lexError :: String -> Parser a
lexError msg =
    do	p <- parsePos <$> get
	parseErrorAt p msg

{--------------------------------------------------------------------------
    Layout
 --------------------------------------------------------------------------}

getContext :: Parser [LayoutContext]
getContext = parseLayout <$> get

setContext :: [LayoutContext] -> Parser ()
setContext ctx =
    do	s <- get
	put $ s { parseLayout = ctx }

-- | Return the current layout context.
topContext :: Parser LayoutContext
topContext =
    do	ctx <- getContext
	case ctx of
	    []  -> parseError "No layout context in scope"
	    l:_ -> return l

popContext :: Parser ()
popContext =
    do	ctx <- getContext
	case ctx of
	    []	    -> parseError "There is no layout block to close at this point."
	    _:ctx   -> setContext ctx

pushContext :: LayoutContext -> Parser ()
pushContext l =
    do	ctx <- getContext
	setContext (l : ctx)

-- | Should only be used at the beginning of a file. When we start parsing
--   we should be in layout mode. Instead of forcing zero indentation we use
--   the indentation of the first token.
pushCurrentContext :: Parser ()
pushCurrentContext =
    do	p <- getLastPos
	pushContext (Layout (posCol p))
