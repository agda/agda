
module Syntax.Parser
    ( -- * Parse functions
      Syntax.Parser.parse
    , Syntax.Parser.parseFile
    , parseLiterate
    , parseLiterateFile
      -- * Parsers
    , tokensParser
      -- * Parse results
    , ParseResult(..)
    , ParseError(..)
    ) where

import Syntax.Parser.Monad as Monad
import Syntax.Parser.Parser
import Syntax.Parser.Lexer

parse :: Parser a -> String -> ParseResult a
parse p = Monad.parse defaultParseFlags normal p

parseFile :: Parser a -> FilePath -> IO (ParseResult a)
parseFile p = Monad.parseFile defaultParseFlags normal p

parseLiterate :: Parser a -> String -> ParseResult a
parseLiterate p = Monad.parse defaultParseFlags literate p

parseLiterateFile :: Parser a -> FilePath -> IO (ParseResult a)
parseLiterateFile p = Monad.parseFile defaultParseFlags literate p


