
module Syntax.Parser
    ( -- * Types
      M.Parser
      -- * Parse functions
    , Syntax.Parser.parse
    , Syntax.Parser.parsePosString
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

import Syntax.Position
import Syntax.Parser.Monad as M
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
parse p = wrap . M.parse defaultParseFlags normal p

parseFile :: Parser a -> FilePath -> IO a
parseFile p = wrapM . M.parseFile defaultParseFlags normal p

parseLiterate :: Parser a -> String -> a
parseLiterate p = wrap . M.parse defaultParseFlags literate p

parseLiterateFile :: Parser a -> FilePath -> IO a
parseLiterateFile p = wrapM . M.parseFile defaultParseFlags literate p


parsePosString :: Parser a -> Position -> String -> a
parsePosString p pos = wrap . M.parsePosString pos defaultParseFlags normal p
