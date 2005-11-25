
module Syntax.Parser
    ( -- * Parse functions
      Syntax.Parser.parse
    , Syntax.Parser.parseFile
    , parseLiterate
    , parseLiterateFile
      -- * Parsers
    , moduleParser
    , exprParser
    , tokensParser
    , interfaceParser
      -- * Parse errors
    , ParseError(..)
    ) where

import Control.Exception

import Syntax.Parser.Monad as Monad
import Syntax.Parser.Parser
import Syntax.Parser.Lexer

-- Wrapping parse results -------------------------------------------------

wrap :: ParseResult a -> a
wrap (ParseOk _ x)	= x
wrap (ParseFailed err)	= throwDyn err

wrapM:: Monad m => m (ParseResult a) -> m a
wrapM m =
    do	r <- m
	case r of
	    ParseOk _ x	    -> return x
	    ParseFailed err -> throwDyn err

-- Parse functions --------------------------------------------------------

parse :: Parser a -> String -> a
parse p = wrap . Monad.parse defaultParseFlags normal p

parseFile :: Parser a -> FilePath -> IO a
parseFile p = wrapM . Monad.parseFile defaultParseFlags normal p

parseLiterate :: Parser a -> String -> a
parseLiterate p = wrap . Monad.parse defaultParseFlags literate p

parseLiterateFile :: Parser a -> FilePath -> IO a
parseLiterateFile p = wrapM . Monad.parseFile defaultParseFlags literate p


