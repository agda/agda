{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Agda.Syntax.Parser
    ( -- * Types
      Parser
      -- * Parse functions
    , Agda.Syntax.Parser.parse
    , Agda.Syntax.Parser.parsePosString
    , parseFile
      -- * Parsers
    , moduleParser
    , moduleNameParser
    , acceptableFileExts
    , exprParser
    , exprWhereParser
    , holeContentParser
    , tokensParser
      -- * Reading files.
    , readFilePM
      -- * Parse errors
    , ParseError(..)
    , ParseWarning(..)
    , PM(..)
    , runPMIO
    ) where

import Control.Arrow (second)
import Control.Exception
import Control.Monad (forM_)
import Control.Monad.State

import qualified Data.List as List
import Data.Text.Lazy (Text)

import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Syntax.Parser.Monad as M hiding (Parser, parseFlags)
import qualified Agda.Syntax.Parser.Monad as M
import qualified Agda.Syntax.Parser.Parser as P
import Agda.Syntax.Parser.Lexer
import Agda.Syntax.Parser.Literate
import Agda.Syntax.Concrete
import Agda.Syntax.Parser.Tokens

import Agda.Utils.Except
  ( ExceptT
  , MonadError(throwError)
  , runExceptT
  )
import Agda.Utils.FileName
import Agda.Utils.IO.UTF8 (readTextFile)
import qualified Agda.Utils.Maybe.Strict as Strict
import Agda.Utils.Pretty ()

------------------------------------------------------------------------
-- Wrapping parse results

wrap :: ParseResult a -> PM a
wrap (ParseOk _ x)      = return x
wrap (ParseFailed err)  = throwError err

wrapIOM :: (MonadError e m, MonadIO m) => (IOError -> e) -> IO a -> m a
wrapIOM f m = do
  a <- liftIO$ (Right <$> m) `catch` (\err -> return$ Left (err :: IOError))
  case a of
    Right x  -> return x
    Left err -> throwError (f err)

wrapM :: IO (ParseResult a) -> PM a
wrapM m = liftIO m >>= wrap

-- | A monad for handling parse results
newtype PM a = PM { unPM :: ExceptT ParseError (StateT [ParseWarning] IO) a }
               deriving (Functor, Applicative, Monad,
                         MonadError ParseError, MonadIO)

warning :: ParseWarning -> PM ()
warning w = PM (modify (w:))

runPMIO :: (MonadIO m) => PM a -> m (Either ParseError a, [ParseWarning])
runPMIO = liftIO . fmap (second reverse) . flip runStateT [] . runExceptT . unPM

------------------------------------------------------------------------
-- Parse functions

-- | Wrapped Parser type.

data Parser a = Parser
  { parser         :: M.Parser a
  , parseFlags     :: ParseFlags
  , parseLiterate  :: LiterateParser a
  }

type LiterateParser a = Parser a -> [Layer] -> PM a

parse :: Parser a -> String -> PM a
parse p = wrapM . return . M.parse (parseFlags p) [normal] (parser p)

parseStringFromFile :: SrcFile -> Parser a -> String -> PM a
parseStringFromFile src p = wrapM . return . M.parseFromSrc (parseFlags p) [layout, normal] (parser p) src

parseLiterateWithoutComments :: LiterateParser a
parseLiterateWithoutComments p layers = parseStringFromFile (literateSrcFile layers) p $ illiterate layers

parseLiterateWithComments :: LiterateParser [Token]
parseLiterateWithComments p layers = do
  code <- map Left <$> parseLiterateWithoutComments p layers
  let literate = Right <$> filter (not . isCodeLayer) layers
  let (terms, overlaps) = interleaveRanges code literate
  forM_ (map fst overlaps) $ \c ->
    warning$ OverlappingTokensWarning { warnRange = getRange c }

  return$ concat [ case m of
                       Left t -> [t]
                       Right (Layer Comment interval s) -> [TokTeX (interval, s)]
                       Right (Layer Markup interval s) -> [TokMarkup (interval, s)]
                       Right (Layer Code _ _) -> []
                   | m <- terms ]

-- | Returns the contents of the given file.

readFilePM :: AbsolutePath -> PM Text
readFilePM path = wrapIOM (ReadFileError path) (readTextFile $ filePath path)

parseLiterateFile
  :: Processor
  -> Parser a
  -> AbsolutePath
     -- ^ The path to the file.
  -> String
     -- ^ The file contents. Note that the file is /not/ read from
     -- disk.
  -> PM a
parseLiterateFile po p path = parseLiterate p p . po (startPos (Just path))

parsePosString :: Parser a -> Position -> String -> PM a
parsePosString p pos = wrapM . return . M.parsePosString pos (parseFlags p) [normal] (parser p)

-- | Extensions supported by `parseFile`.

acceptableFileExts :: [String]
acceptableFileExts = ".agda" : (fst <$> literateProcessors)

parseFile
  :: Show a
  => Parser a
  -> AbsolutePath
     -- ^ The path to the file.
  -> String
     -- ^ The file contents. Note that the file is /not/ read from
     -- disk.
  -> PM (a, FileType)
parseFile p file input =
  if ".agda" `List.isSuffixOf` filePath file then
    (, AgdaFileType) <$> Agda.Syntax.Parser.parseStringFromFile
                         (Strict.Just file) p input
  else
    go literateProcessors
  where
    go [] = throwError InvalidExtensionError
                   { errPath = file
                   , errValidExts = acceptableFileExts
                   }
    go ((ext, (po, ft)) : pos)
      | ext `List.isSuffixOf` filePath file =
          (, ft) <$> parseLiterateFile po p file input
      | otherwise = go pos

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

-- | Parses an expression or some other content of an interaction hole.

holeContentParser :: Parser HoleContent
holeContentParser = Parser
  { parser        = P.holeContentParser
  , parseFlags    = withoutComments
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
