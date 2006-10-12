
module Syntax.Parser
    ( -- * Types
      M.Parser
      -- * Parse functions
    , Syntax.Parser.parse
    , Syntax.Parser.parsePosString
    , Syntax.Parser.parseFile
    , parseFile'
    , parseLiterate
    , parseLiterateFile
      -- * Parsers
    , moduleParser
    , exprParser
    , tokensParser
      -- * Parse errors
    , ParseError(..)
    ) where

import Control.Exception
import Data.List

import Syntax.Position
import Syntax.Parser.Monad as M
import Syntax.Parser.Parser
import Syntax.Parser.Lexer
import Syntax.Strict

-- Wrapping parse results -------------------------------------------------

wrap :: Strict a => ParseResult a -> a
wrap (ParseOk _ x)	= x
wrap (ParseFailed err)	= throwDyn err

wrapM:: (Strict a, Monad m) => m (ParseResult a) -> m a
wrapM m =
    do	r <- m
	case r of
	    ParseOk _ x	    -> return x
	    ParseFailed err -> throwDyn err

-- Parse functions --------------------------------------------------------

parse :: Strict a => Parser a -> String -> IO a
parse p = wrapM . return . M.parse defaultParseFlags normal p

parseFile :: Strict a => Parser a -> FilePath -> IO a
parseFile p = wrapM . M.parseFile defaultParseFlags normal p

parseLiterate :: Strict a => Parser a -> String -> IO a
parseLiterate p = wrapM . return . M.parse defaultParseFlags literate p

parseLiterateFile :: Strict a => Parser a -> FilePath -> IO a
parseLiterateFile p = wrapM . M.parseFile defaultParseFlags literate p

parsePosString :: Strict a => Parser a -> Position -> String -> IO a
parsePosString p pos = wrapM . return . M.parsePosString pos defaultParseFlags normal p

parseFile' :: Strict a => Parser a -> FilePath -> IO a
parseFile' p file
    | "lagda" `isSuffixOf` file	= Syntax.Parser.parseLiterateFile p file
    | otherwise			= Syntax.Parser.parseFile p file
 

