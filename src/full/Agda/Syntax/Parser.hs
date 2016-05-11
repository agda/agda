{-# LANGUAGE CPP #-}

module Agda.Syntax.Parser
    ( -- * Types
      Parser
      -- * Parse functions
    , Agda.Syntax.Parser.parse
    , Agda.Syntax.Parser.parsePosString
    , parseFile'
      -- * Parsers
    , moduleParser
    , moduleNameParser
    , exprParser
    , exprWhereParser
    , tokensParser
      -- * Parse errors
    , ParseError(..)
    ) where

import Control.Exception
import Control.Monad ((>=>), forM_)
import Data.List

import Agda.Syntax.Position
import Agda.Syntax.Parser.Monad as M hiding (Parser, parseFlags)
import qualified Agda.Syntax.Parser.Monad as M
import qualified Agda.Syntax.Parser.Parser as P
import Agda.Syntax.Parser.Lexer
import Agda.Syntax.Parser.Literate
import Agda.Syntax.Concrete
import Agda.Syntax.Concrete.Definitions
import Agda.Syntax.Parser.Tokens

import Agda.Utils.Except ( MonadError(throwError) )
import Agda.Utils.FileName
import qualified Agda.Utils.Maybe.Strict as Strict

#if __GLASGOW_HASKELL__ <= 708
import Control.Applicative ((<$>))
#endif

#include "undefined.h"
import Agda.Utils.Impossible

------------------------------------------------------------------------
-- Wrapping parse results

wrap :: ParseResult a -> a
wrap (ParseOk _ x)      = x
wrap (ParseFailed err)  = throw err

wrapM:: Monad m => m (ParseResult a) -> m a
wrapM m =
    do  r <- m
        case r of
            ParseOk _ x     -> return x
            ParseFailed err -> throw err

------------------------------------------------------------------------
-- Parse functions

-- | Wrapped Parser type.

data Parser a = Parser
  { parser         :: M.Parser a
  , parseFlags     :: ParseFlags
  , parseLiterate  :: LiterateParser a
  }

type LiterateParser a = Parser a -> [Layer] -> IO a

parse :: Parser a -> String -> IO a
parse p = wrapM . return . M.parse (parseFlags p) [normal] (parser p)

parseFile :: Parser a -> AbsolutePath -> IO a
parseFile p = wrapM . M.parseFile (parseFlags p) [layout, normal] (parser p)

parseString :: Parser a -> String -> IO a
parseString = parseStringFromFile Strict.Nothing

parseStringFromFile :: SrcFile -> Parser a -> String -> IO a
parseStringFromFile src p = wrapM . return . M.parseFromSrc (parseFlags p) [layout, normal] (parser p) src

parseLiterateWithoutComments :: LiterateParser a
parseLiterateWithoutComments p layers = parseStringFromFile (literateSrcFile layers) p $ illiterate layers

parseLiterateWithComments :: LiterateParser [Token]
parseLiterateWithComments p layers = do
  code <- map Left <$> parseLiterateWithoutComments p layers
  let markup = Right <$> filter (not . isCode) layers
  let (terms, overlaps) = interleaveRanges code markup
  forM_ overlaps $ \(c,_) ->
    fail$ "Multiline token in literate file spans multiple code blocks " ++ show (getRange c)
  return$ concat [ case m of
                     Left t -> [t]
                     Right (Layer Comment interval s) -> [TokTeX (interval, s)]
                     Right (Layer Markup _ _) -> []
                     Right (Layer Code _ _) -> []
                 | m <- terms ]

parseLiterateFile :: Processor -> Parser a -> AbsolutePath -> IO a
parseLiterateFile po p path = readFile (filePath path) >>= parseLiterate p p . po (startPos (Just path))

parsePosString :: Parser a -> Position -> String -> IO a
parsePosString p pos = wrapM . return . M.parsePosString pos (parseFlags p) [normal] (parser p)

parseFile' :: (Show a) => Parser a -> AbsolutePath -> IO a
parseFile' p file =
  if ".agda" `isSuffixOf` filePath file then
    Agda.Syntax.Parser.parseFile p file
  else
    go literateProcessors
  where
    go [] = fail$ "Unsupported extension for file " ++ filePath file
    go ((ext, po):pos) | ext `isSuffixOf` filePath file = parseLiterateFile po p file
    go (_:pos) = go pos


------------------------------------------------------------------------
-- Specific parsers

-- | Parses a module.

moduleParser :: Parser Module
moduleParser = Parser { parser = P.moduleParser
                      , parseFlags = withoutComments
                      , parseLiterate = parseLiterateWithoutComments
                      }

-- | Parses a module name.

moduleNameParser :: Parser QName
moduleNameParser = Parser { parser = P.moduleNameParser
                          , parseFlags = withoutComments
                          , parseLiterate = parseLiterateWithoutComments
                          }

-- | Parses an expression.

exprParser :: Parser Expr
exprParser = Parser { parser = P.exprParser
                    , parseFlags = withoutComments
                    , parseLiterate = parseLiterateWithoutComments
                    }

-- | Parses an expression followed by a where clause.

exprWhereParser :: Parser ExprWhere
exprWhereParser = Parser
  { parser     = P.exprWhereParser
  , parseFlags = withoutComments
  , parseLiterate = parseLiterateWithoutComments
  }

-- | Gives the parsed token stream (including comments).

tokensParser :: Parser [Token]
tokensParser = Parser { parser = P.tokensParser
                      , parseFlags = withComments
                      , parseLiterate = parseLiterateWithComments
                      }

-- | Keep comments in the token stream generated by the lexer.

withComments :: ParseFlags
withComments = defaultParseFlags { parseKeepComments = True }

-- | Do not keep comments in the token stream generated by the lexer.

withoutComments :: ParseFlags
withoutComments = defaultParseFlags { parseKeepComments = False }
