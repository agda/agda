
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

import Control.Exception
import Control.Monad          ( forM_ )
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.IO.Class ( MonadIO(..) )

import Data.Bifunctor
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
import Agda.Syntax.Concrete.Attribute
import Agda.Syntax.Parser.Tokens

import Agda.Utils.FileName
import Agda.Utils.IO.UTF8 (readTextFile)
import Agda.Utils.Maybe   (forMaybe)
import qualified Agda.Utils.Maybe.Strict as Strict

------------------------------------------------------------------------
-- Wrapping parse results

-- | A monad for handling parse errors and warnings.

newtype PM a = PM { unPM :: ExceptT ParseError (StateT [ParseWarning] IO) a }
  deriving ( Functor, Applicative, Monad, MonadIO
           , MonadError ParseError, MonadState [ParseWarning]
           )

-- | Run a 'PM' computation, returning a list of warnings in first-to-last order
--   and either a parse error or the parsed thing.

runPMIO :: (MonadIO m) => PM a -> m (Either ParseError a, [ParseWarning])
runPMIO = liftIO . fmap (second reverse) . flip runStateT [] . runExceptT . unPM

-- | Add a 'ParseWarning'.

warning :: ParseWarning -> PM ()
warning w = PM (modify (w:))

-- | Embed a 'ParseResult' as 'PM' computation.

wrap :: ParseResult a -> PM (a, Attributes)
wrap (ParseFailed err)  = throwError err
wrap (ParseOk s x)      = do
  modify' (parseWarnings s ++)
  return (x, parseAttributes s)

wrapM :: IO (ParseResult a) -> PM (a, Attributes)
wrapM m = liftIO m >>= wrap

-- | Returns the contents of the given file.

readFilePM :: RangeFile -> PM Text
readFilePM file =
  wrapIOM (ReadFileError file) $
  readTextFile (filePath $ rangeFilePath file)

wrapIOM :: (MonadError e m, MonadIO m) => (IOError -> e) -> IO a -> m a
wrapIOM f m = do
  a <- liftIO$ (Right <$> m) `catch` (\err -> return$ Left (err :: IOError))
  case a of
    Right x  -> return x
    Left err -> throwError (f err)

------------------------------------------------------------------------
-- Parse functions

-- | Wrapped Parser type.

data Parser a = Parser
  { parser         :: M.Parser a
  , parseFlags     :: ParseFlags
  , parseLiterate  :: LiterateParser a
  }

type LiterateParser a =
  Parser a -> [Layer] -> PM (a, Attributes)

-- | Initial state for lexing.

normalLexState :: [LexState]
normalLexState = [normal]

-- | Initial state for lexing with top-level layout.

layoutLexState :: [LexState]
layoutLexState = [layout, normal]

-- | Parse without top-level layout.

parse :: Parser a -> String -> PM (a, Attributes)
parse p = wrapM . return . M.parse (parseFlags p) normalLexState (parser p)

-- | Parse with top-level layout.

parseFileFromString
  :: SrcFile   -- ^ Name of source file.
  -> Parser a  -- ^ Parser to use.
  -> String    -- ^ Contents of source file.
  -> PM (a, Attributes)
parseFileFromString src p = wrapM . return . M.parseFromSrc (parseFlags p) layoutLexState (parser p) src

-- | Parse with top-level layout.

parseLiterateWithoutComments :: LiterateParser a
parseLiterateWithoutComments p layers = parseFileFromString (literateSrcFile layers) p $ illiterate layers

-- | Parse with top-level layout.

parseLiterateWithComments :: LiterateParser [Token]
parseLiterateWithComments p layers = do
  (code, coh) <- parseLiterateWithoutComments p layers
  let literate = filter (not . isCodeLayer) layers
  let (terms, overlaps) = interleaveRanges (map Left code) (map Right literate)

  forM_ (map fst overlaps) $ \c ->
    warning $ OverlappingTokensWarning { warnRange = getRange c }

  (, coh) <$> (return $ forMaybe terms $ \case
    Left t                           -> Just t
    Right (Layer Comment interval s) -> Just $ TokTeX    (interval, s)
    Right (Layer Markup  interval s) -> Just $ TokMarkup (interval, s)
    Right (Layer Code _ _)           -> Nothing)


parseLiterateFile
  :: Processor
  -> Parser a
  -> RangeFile
     -- ^ The file.
  -> String
     -- ^ The file contents. Note that the file is /not/ read from
     -- disk.
  -> PM (a, Attributes)
parseLiterateFile po p path = parseLiterate p p . po (startPos (Just path))

parsePosString ::
  Parser a -> Position -> String -> PM (a, Attributes)
parsePosString p pos = wrapM . return . M.parsePosString pos (parseFlags p) normalLexState (parser p)

-- | Extensions supported by `parseFile`.

acceptableFileExts :: [String]
acceptableFileExts = ".agda" : (fst <$> literateProcessors)

parseFile
  :: Show a
  => Parser a
  -> RangeFile
     -- ^ The file.
  -> String
     -- ^ The file contents. Note that the file is /not/ read from
     -- disk.
  -> PM ((a, Attributes), FileType)
parseFile p file input =
  if ".agda" `List.isSuffixOf` path then
    (, AgdaFileType) <$> parseFileFromString (Strict.Just file) p input
  else
    go literateProcessors
  where
    path = filePath (rangeFilePath file)

    go [] = throwError InvalidExtensionError
                   { errPath = file
                   , errValidExts = acceptableFileExts
                   }
    go ((ext, (po, ft)) : pos)
      | ext `List.isSuffixOf` path =
          (, ft) <$> parseLiterateFile po p file input
      | otherwise = go pos

------------------------------------------------------------------------
-- Specific parsers

-- | Parses a module.

moduleParser :: Parser Module
moduleParser = Parser
  { parser        = P.moduleParser
  , parseFlags    = withoutComments
  , parseLiterate = parseLiterateWithoutComments
  }

-- | Parses a module name.

moduleNameParser :: Parser QName
moduleNameParser = Parser
  { parser        = P.moduleNameParser
  , parseFlags    = withoutComments
  , parseLiterate = parseLiterateWithoutComments
  }

-- | Parses an expression.

exprParser :: Parser Expr
exprParser = Parser
  { parser        = P.exprParser
  , parseFlags    = withoutComments
  , parseLiterate = parseLiterateWithoutComments
  }

-- | Parses an expression followed by a where clause.

exprWhereParser :: Parser ExprWhere
exprWhereParser = Parser
  { parser        = P.exprWhereParser
  , parseFlags    = withoutComments
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
tokensParser = Parser
  { parser        = P.tokensParser
  , parseFlags    = withComments
  , parseLiterate = parseLiterateWithComments
  }

-- | Keep comments in the token stream generated by the lexer.

withComments :: ParseFlags
withComments = defaultParseFlags { parseKeepComments = True }

-- | Do not keep comments in the token stream generated by the lexer.

withoutComments :: ParseFlags
withoutComments = defaultParseFlags { parseKeepComments = False }
