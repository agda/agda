{-# OPTIONS -fglasgow-exts #-}

module Syntax.Parser.Monad
    ( -- * The parser monad
      Parser
    , ParseResult(..)
    , ParseState(..)
    , ParseError(..)
    , LexState
    , LayoutContext(..)
    , ParseFlags
      -- * Running the parser
    , initState
    , defaultParseFlags
    , parse'
    , parseFile'
      -- * Manipulating the state
    , setLastPos, getParseRange
    , setPrevToken
    , getParseFlags
    , getLexState, pushLexState, popLexState
      -- ** Layout
    , topContext, popContext, pushContext
    , pushCurrentContext, getOffside
      -- ** Errors
    , parseError
    )
    where

import Data.Char

import Control.Monad.State
import Control.Monad.Error

import Syntax.Position

import Utils.Monads
import Utils.Unicode

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

-- | To do context sensitive lexing alex provides what is called /start
--   codes/ in the Alex documentation. It is really an integer
--   representing the state of the lexer, so we call it @LexState@ instead
--   of start code.
type LexState = Int

-- | We need to keep track of the context to do layout. The context
--   specifies the indentation of the current (if any) layout block.
data LayoutContext  = NoLayout	    -- ^ no layout
		    | Layout Int    -- ^ layout at specified column
    deriving Show

-- | There aren't any parser flags at the moment.
type ParseFlags	= ()

-- | What you get if parsing fails.
data ParseError	= ParseError
		    { errPos	    :: Position	-- ^ where the error occured
		    , errInput	    :: String	-- ^ the remaining input
		    , errPrevToken  :: String	-- ^ the previous token
		    , errMsg	    :: String	-- ^ hopefully an explanation
						--   of what happened
		    }

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
				ParseError  { errPos	    = parsePos s
					    , errInput	    = parseInp s
					    , errPrevToken  = parsePrevToken s
					    , errMsg	    = msg
					    }

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
	    , replicate (length pos + 2) ' ' ++ showInp (errInput err)
	    ]
	where
	    pos = show (errPos err)

	    showInp ""  = "at end of file"
	    showInp t   = "on input '" ++ elide 10 t ++ "'"

	    elide 3 s
		| length (take 4 s) < 4 = s
		| otherwise		    = "..."
	    elide n (c:s)		    = c : elide (n - 1) s
	    elide _ ""		    = ""


{--------------------------------------------------------------------------
    Running the parser
 --------------------------------------------------------------------------}

-- | Constructs the initial state of the parser. The string argument
--   is the input string, the file path is only there because it's part
--   of a position.
initState :: FilePath -> ParseFlags -> String -> LexState -> ParseState
initState file flags inp st =
	PState  { parsePos	    = p
		, parseLastPos	    = p
		, parseInp	    = inp
		, parsePrevChar	    = '\n'
		, parsePrevToken    = ""
		, parseLexState	    = [st]
		, parseLayout	    = []
		, parseFlags	    = flags
		}
    where
	p = startPos file

-- | The default flags.
defaultParseFlags :: ParseFlags
defaultParseFlags = ()

-- | The most general way of parsing a string. The "Parser" will define
--   more specialised functions that supply the 'ParseFlags' and the
--   'LexState'.
parse' :: ParseFlags -> LexState -> Parser a -> String -> ParseResult a
parse' flags st p input = unP p (initState "" flags input st)

-- | The most general way of parsing a file. The "Parser" will define
--   more specialised functions that supply the 'ParseFlags' and the
--   'LexState'.
parseFile' :: ParseFlags -> LexState -> Parser a -> FilePath -> IO (ParseResult a)
parseFile' flags st p file =
    do	input <- liftIO $ readFileUTF8 file
	return $ unP p (initState file flags input st)

{--------------------------------------------------------------------------
    Manipulating the state
 --------------------------------------------------------------------------}

setLastPos :: Position -> Parser ()
setLastPos p = modify $ \s -> s { parseLastPos = p }

setPrevToken :: String -> Parser ()
setPrevToken t = modify $ \s -> s { parsePrevToken = t }

getLastPos :: Parser Position
getLastPos = get >>= return . parseLastPos

-- | The parse range is between the last position and the current position.
getParseRange :: Parser Range
getParseRange =
    do	s <- get
	return $ Range (parseLastPos s) (parsePos s)

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

{--------------------------------------------------------------------------
    Layout
 --------------------------------------------------------------------------}

getContext :: Parser [LayoutContext]
getContext = parseLayout <$> get

setContext :: [LayoutContext] -> Parser ()
setContext ctx =
    do	s <- get
	put $ s { parseLayout = ctx }

-- | The context stack is never empty, so this function always succeeds.
topContext :: Parser LayoutContext
topContext = head . parseLayout <$> get

popContext :: Parser ()
popContext =
    do	_:ctx <- getContext
	setContext ctx

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

