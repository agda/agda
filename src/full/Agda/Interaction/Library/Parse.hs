-- | Parser for @.agda-lib@ files.
--
--   Example file:
--
--   @
--     name: Main
--     depend:
--       standard-library
--     include: .
--       src more-src
--
--   @
--
--   Should parse as:
--
--   @
--     AgdaLib
--       { libName     = "Main"
--       , libFile     = path_to_this_file
--       , libIncludes = [ "." , "src" , "more-src" ]
--       , libDepends  = [ "standard-library" ]
--       }
--   @
--
module Agda.Interaction.Library.Parse
  ( parseLibFile
  , splitCommas
  , trimLineComment
  , runP
  ) where

import Control.Monad
import Control.Monad.Except
import Control.Monad.Writer
import Data.Char
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)
import qualified Data.Text as T
import System.FilePath

import Agda.Interaction.Library.Base

import Agda.Syntax.Position

import Agda.Utils.Applicative
import Agda.Utils.FileName
import Agda.Utils.IO                ( catchIO )
import qualified Agda.Utils.IO.UTF8 as UTF8
import Agda.Utils.Lens
import Agda.Utils.List              ( duplicates )
import Agda.Utils.List1             ( List1, toList )
import qualified Agda.Utils.List1   as List1
import qualified Agda.Utils.Maybe.Strict as Strict
import Agda.Utils.Singleton
import Agda.Utils.String            ( ltrim )

-- | Parser monad: Can throw @LibParseError@s, and collects
-- @LibWarning'@s library warnings.
type P = ExceptT LibParseError (Writer [LibWarning'])

runP :: P a -> (Either LibParseError a, [LibWarning'])
runP = runWriter . runExceptT

warningP :: LibWarning' -> P ()
warningP = tell . pure

-- | The config files we parse have the generic structure of a sequence
--   of @field : content@ entries.
type GenericFile = [GenericEntry]

data GenericEntry = GenericEntry
  { geHeader   :: String        -- ^ E.g. field name.    @trim@med.
  , _geContent :: [ContentLine] -- ^ E.g. field content. @trim@med.
  }

-- | A (part of a) line of field content.
data ContentLine = ContentLine
  { clLine   :: LineNumber
  , clColumn :: Int     -- ^ Column (1-based) where 'clText' starts.
  , clText   :: String  -- ^ @trim@med.
  }
  deriving (Show)

-- | Library file field format format [sic!].
data Field = forall a. Field
  { fName     :: String
      -- ^ Name of the field.
  , fOptional :: Bool
      -- ^ Is it optional?
  , fParse    :: Range -> [ContentLine] -> P a
      -- ^ Content parser for this field.
      --
      -- The range points to the start of the file.
  , fSet      :: LensSet AgdaLibFile a
      -- ^ Sets parsed content in 'AgdaLibFile' structure.
  }

optionalField ::
  String -> (Range -> [ContentLine] -> P a) -> Lens' AgdaLibFile a -> Field
optionalField str p l = Field str True p (set l)

-- | @.agda-lib@ file format with parsers and setters.
agdaLibFields :: [Field]
agdaLibFields =
  -- Andreas, 2017-08-23, issue #2708, field "name" is optional.
  [ optionalField "name"    (\_ -> parseName . map clText)                     libName
  , optionalField "include" (\_ -> pure . concatMap (parsePaths . clText))   libIncludes
  , Field "depend" True     (\_ -> pure . parseDepends)
      (\ (ds, pos) l -> l{ _libDepends = ds, _libDependsPos = pos })
  , optionalField "flags"   (\r -> pure . foldMap (parseFlags r . clText)) libPragmas
  ]
  where
    -- Remember where the dependencies are mentioned (issue #8875).
    parseDepends :: [ContentLine] -> ([LibName], Map LibName LibFilePos)
    parseDepends cls = (map fst ds, Map.fromListWith (\ _new old -> old) ds)
      where
        ds = [ (parseLibName w, LibFilePos l c (c + length w))
             | ContentLine l c0 s <- cls
             , (c, w) <- splitCommasPos c0 s
             ]

    parseName :: [String] -> P LibName
    parseName [s] | [name] <- words s = pure $ parseLibName name
    parseName ls = throwError $ BadLibraryName $ unwords ls

    parsePaths :: String -> [FilePath]
    parsePaths = go id where
      fixup acc = let fp = acc [] in not (null fp) ?$> fp
      go acc []           = fixup acc
      go acc ('\\' : ' '  :cs) = go (acc . (' ':)) cs
      go acc ('\\' : '\\' :cs) = go (acc . ('\\':)) cs
      go acc (       ' '  :cs) = fixup acc ++ go id cs
      go acc (c           :cs) = go (acc . (c:)) cs

    parseFlags :: Range -> String -> OptionsPragma
    parseFlags r s = OptionsPragma
      { pragmaStrings = words s
      , pragmaRange   = r
      }

-- | Parse @.agda-lib@ file.
--
-- Sets 'libFile' name and turn mentioned include directories into absolute
-- pathes (provided the given 'FilePath' is absolute).
--
parseLibFile :: FilePath -> IO (P AgdaLibFile)
parseLibFile file = do
  abs <- absolute file
  (fmap setPath . parseLib abs <$> UTF8.readFile file) `catchIO` \e ->
    return $ throwError $ ReadFailure file e
  where
    setPath      lib = unrelativise (takeDirectory file) (set libFile file lib)
    unrelativise dir = over libIncludes (map (dir </>))

-- | Parse file contents.
parseLib
  :: AbsolutePath
     -- ^ The parsed file.
  -> String
  -> P AgdaLibFile
parseLib file s = fromGeneric file =<< parseGeneric s

-- | Parse 'GenericFile' with 'agdaLibFields' descriptors.
fromGeneric
  :: AbsolutePath
     -- ^ The parsed file.
  -> GenericFile
  -> P AgdaLibFile
fromGeneric file = fromGeneric' file agdaLibFields

-- | Given a list of 'Field' descriptors (with their custom parsers),
--   parse a 'GenericFile' into the 'AgdaLibFile' structure.
--
--   Checks mandatory fields are present;
--   no duplicate fields, no unknown fields.

fromGeneric'
  :: AbsolutePath
     -- ^ The parsed file.
  -> [Field]
  -> GenericFile
  -> P AgdaLibFile
fromGeneric' file fields fs = do
  checkFields fields (map geHeader fs)
  foldM upd emptyLibFile fs
  where
    -- The range points to the start of the file.
    r :: Range
    r = beginningOfFile file
    upd :: AgdaLibFile -> GenericEntry -> P AgdaLibFile
    upd l (GenericEntry h cs) = do
      mf <- findField h fields
      case mf of
        Just Field{ fParse, fSet } -> do
          x <- fParse r cs
          return $ fSet x l
        Nothing -> return l

-- | Ensure that there are no duplicate fields and no mandatory fields are missing.
checkFields :: [Field] -> [String] -> P ()
checkFields fields fs = do
  -- Report missing mandatory fields.
  () <- List1.unlessNull missing $ throwError . MissingFields
  -- Report duplicate fields.
  List1.unlessNull (duplicates fs) $ throwError . DuplicateFields
  where
  mandatory :: [String]
  mandatory = [ fName f | f <- fields, not $ fOptional f ]
  missing   :: [String]
  missing   = mandatory List.\\ fs

-- | Find 'Field' with given 'fName', throw error if unknown.
findField :: String -> [Field] -> P (Maybe Field)
findField s fs = maybe err (return . Just) $ List.find ((s ==) . fName) fs
  where err = warningP (UnknownField s) >> return Nothing

-- Generic file parser ----------------------------------------------------

-- | Example:
--
-- @
--     parseGeneric "name:Main--BLA\ndepend:--BLA\n  standard-library--BLA\ninclude : . --BLA\n  src more-src   \n"
--     == Right [("name",["Main"]),("depend",["standard-library"]),("include",[".","src more-src"])]
-- @
parseGeneric :: String -> P GenericFile
parseGeneric s =
  groupLines =<< concat <$> zipWithM parseLine [1..] (map stripComments $ lines s)

-- | Lines with line numbers.
data GenericLine
  = Header  LineNumber String
      -- ^ Header line, like a field name, e.g. "include :".  Cannot be indented.
      --   @String@ is 'trim'med.
  | Content ContentLine
      -- ^ Other line.  Must be indented.
  deriving (Show)

-- | Parse line into 'Header' and 'Content' components.
--
--   Precondition: line comments and trailing whitespace have been stripped away.
--
--   Example file:
--
--   @
--     name: Main
--     depend:
--       standard-library
--     include: .
--       src more-src
--   @
--
--   This should give
--
--   @
--     [ Header  1 "name"
--     , Content (ContentLine 1 7 "Main")
--     , Header  2 "depend"
--     , Content (ContentLine 3 3 "standard-library")
--     , Header  4 "include"
--     , Content (ContentLine 4 10 ".")
--     , Content (ContentLine 5 3 "src more-src")
--     ]
--   @
parseLine :: LineNumber -> String -> P [GenericLine]
parseLine _ "" = pure []
parseLine l s@(c:_)
    -- Indented lines are 'Content'.
  | isSpace c   = pure [content $ ltrim s]
    -- Non-indented lines are 'Header'.
  | otherwise   =
    case break (== ':') s of
      -- Headers are single words followed by a colon.
      -- Anything after the colon that is not whitespace is 'Content'.
      (h, ':' : r) ->
        case words h of
          [h] -> pure $ Header l h : [content r' | let r' = ltrim r, not (null r')]
          []  -> throwError $ MissingFieldName l
          hs  -> throwError $ BadFieldName l h
      _ -> throwError $ MissingColonForField l (ltrim s)
  where
    -- @r@ is a suffix of @s@.
    content r = Content $ ContentLine l (length s - length r + 1) r

-- | Collect 'Header' and subsequent 'Content's into 'GenericEntry'.
--
--   Leading 'Content's?  That's an error.
--
groupLines :: [GenericLine] -> P GenericFile
groupLines [] = pure []
groupLines (Content c : _) = throwError $ ContentWithoutField $ clLine c
groupLines (Header _ h : ls) = (GenericEntry h [ c | Content c <- cs ] :) <$> groupLines ls1
  where
    (cs, ls1) = span isContent ls
    isContent Content{} = True
    isContent Header{} = False

-- | Remove leading whitespace and line comment.
trimLineComment :: String -> String
trimLineComment = stripComments . ltrim

-- | Break a comma-separated string.  Result strings are @trim@med.
splitCommas :: String -> [String]
splitCommas = map snd . splitCommasPos 1

-- | Break a comma-separated string starting at the given column.
--   Result strings are @trim@med and come with their starting column.
splitCommasPos :: Int -> String -> [(Int, String)]
splitCommasPos c0 = go . zip [c0..]
  where
    go ps = case dropWhile (isSep . snd) ps of
      [] -> []
      ps'@((c, _) : _) -> let (w, rest) = break (isSep . snd) ps' in (c, map snd w) : go rest
    isSep c = c == ',' || isSpace c

-- | ...and trailing, but not leading, whitespace.
stripComments :: String -> String
stripComments "" = ""
stripComments ('-':'-':c:_) | isSpace c = ""
stripComments (c : s) = cons c (stripComments s)
  where
    cons c "" | isSpace c = ""
    cons c s = c : s
