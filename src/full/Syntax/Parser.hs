
module Syntax.Parser
    ( -- * Parse functions
      parse
    , parseFile
    , parseLiterate
    , parseLiterateFile
      -- * Parsers
    , tokensParser
      -- * Parse results
    , ParseResult(..)
    , ParseError(..)
    ) where

import Syntax.Parser.Monad
import Syntax.Parser.Parser
import Syntax.Parser.Lexer

parse :: Parser a -> String -> ParseResult a
parse p = parse' defaultParseFlags normal p

parseFile :: Parser a -> FilePath -> IO (ParseResult a)
parseFile p = parseFile' defaultParseFlags normal p

parseLiterate :: Parser a -> String -> ParseResult a
parseLiterate p = parse' defaultParseFlags literate p

parseLiterateFile :: Parser a -> FilePath -> IO (ParseResult a)
parseLiterateFile p = parseFile' defaultParseFlags literate p


