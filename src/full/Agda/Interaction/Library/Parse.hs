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
import System.FilePath

import Agda.Interaction.Library.Base

import Agda.Utils.Applicative
import Agda.Utils.IO ( catchIO )
import qualified Agda.Utils.IO.UTF8 as UTF8
import Agda.Utils.Lens
import Agda.Utils.List   ( duplicates )
import Agda.Utils.String ( ltrim )

-- | Parser monad: Can throw @String@ error messages, and collects
-- @LibWarning'@s library warnings.
type P = ExceptT String (Writer [LibWarning'])

runP :: P a -> (Either String a, [LibWarning'])
runP = runWriter . runExceptT

warningP :: LibWarning' -> P ()
warningP = tell . pure

-- | The config files we parse have the generic structure of a sequence
--   of @field : content@ entries.
type GenericFile = [GenericEntry]

data GenericEntry = GenericEntry
  { geHeader   :: String   -- ^ E.g. field name.    @trim@med.
  , _geContent :: [String] -- ^ E.g. field content. @trim@med.
  }

-- | Library file field format format [sic!].
data Field = forall a. Field
  { fName     :: String            -- ^ Name of the field.
  , fOptional :: Bool              -- ^ Is it optional?
  , fParse    :: [String] -> P a   -- ^ Content parser for this field.
  , fSet      :: LensSet a AgdaLibFile
    -- ^ Sets parsed content in 'AgdaLibFile' structure.
  }

optionalField :: String -> ([String] -> P a) -> Lens' a AgdaLibFile -> Field
optionalField str p l = Field str True p (set l)

-- | @.agda-lib@ file format with parsers and setters.
agdaLibFields :: [Field]
agdaLibFields =
  -- Andreas, 2017-08-23, issue #2708, field "name" is optional.
  [ optionalField "name"    parseName                      libName
  , optionalField "include" (pure . concatMap parsePaths)  libIncludes
  , optionalField "depend"  (pure . concatMap splitCommas) libDepends
  , optionalField "flags"   (pure . concatMap parseFlags)  libPragmas
  ]
  where
    parseName :: [String] -> P LibName
    parseName [s] | [name] <- words s = pure name
    parseName ls = throwError $ "Bad library name: '" ++ unwords ls ++ "'"

    parsePaths :: String -> [FilePath]
    parsePaths = go id where
      fixup acc = let fp = acc [] in not (null fp) ?$> fp
      go acc []           = fixup acc
      go acc ('\\' : ' '  :cs) = go (acc . (' ':)) cs
      go acc ('\\' : '\\' :cs) = go (acc . ('\\':)) cs
      go acc (       ' '  :cs) = fixup acc ++ go id cs
      go acc (c           :cs) = go (acc . (c:)) cs

    parseFlags :: String -> [String]
    parseFlags = words

-- | Parse @.agda-lib@ file.
--
-- Sets 'libFile' name and turn mentioned include directories into absolute
-- pathes (provided the given 'FilePath' is absolute).
--
parseLibFile :: FilePath -> IO (P AgdaLibFile)
parseLibFile file =
  (fmap setPath . parseLib <$> UTF8.readFile file) `catchIO` \e ->
    return $ throwError $ unlines
      [ "Failed to read library file " ++ file ++ "."
      , "Reason: " ++ show e
      ]
  where
    setPath      lib = unrelativise (takeDirectory file) (set libFile file lib)
    unrelativise dir = over libIncludes (map (dir </>))

-- | Parse file contents.
parseLib :: String -> P AgdaLibFile
parseLib s = fromGeneric =<< parseGeneric s

-- | Parse 'GenericFile' with 'agdaLibFields' descriptors.
fromGeneric :: GenericFile -> P AgdaLibFile
fromGeneric = fromGeneric' agdaLibFields

-- | Given a list of 'Field' descriptors (with their custom parsers),
--   parse a 'GenericFile' into the 'AgdaLibFile' structure.
--
--   Checks mandatory fields are present;
--   no duplicate fields, no unknown fields.

fromGeneric' :: [Field] -> GenericFile -> P AgdaLibFile
fromGeneric' fields fs = do
  checkFields fields (map geHeader fs)
  foldM upd emptyLibFile fs
  where
    upd :: AgdaLibFile -> GenericEntry -> P AgdaLibFile
    upd l (GenericEntry h cs) = do
      mf <- findField h fields
      case mf of
        Just Field{..} -> do
          x <- fParse cs
          return $ fSet x l
        Nothing -> return l

-- | Ensure that there are no duplicate fields and no mandatory fields are missing.
checkFields :: [Field] -> [String] -> P ()
checkFields fields fs = do
  let mandatory = [ fName f | f <- fields, not $ fOptional f ]
      -- Missing fields.
      missing   = mandatory List.\\ fs
      -- Duplicate fields.
      dup       = duplicates fs
      -- Plural s for error message.
      s xs      = if length xs > 1 then "s" else ""
      list xs   = List.intercalate ", " [ "'" ++ f ++ "'" | f <- xs ]
  unless (null missing) $ throwError $ "Missing field" ++ s missing ++ " " ++ list missing
  unless (null dup)     $ throwError $ "Duplicate field" ++ s dup ++ " " ++ list dup

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
  | Content LineNumber String
      -- ^ Other line.  Must be indented.
      --   @String@ is 'trim'med.
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
--     , Content 1 "Main"
--     , Header  2 "depend"
--     , Content 3 "standard-library"
--     , Header  4 "include"
--     , Content 4 "."
--     , Content 5 "src more-src"
--     ]
--   @
parseLine :: LineNumber -> String -> P [GenericLine]
parseLine _ "" = pure []
parseLine l s@(c:_)
    -- Indented lines are 'Content'.
  | isSpace c   = pure [Content l $ ltrim s]
    -- Non-indented lines are 'Header'.
  | otherwise   =
    case break (==':') s of
      -- Headers are single words followed by a colon.
      -- Anything after the colon that is not whitespace is 'Content'.
      (h, ':' : r) ->
        case words h of
          [h] -> pure $ Header l h : [Content l r' | let r' = ltrim r, not (null r')]
          []  -> throwError $ show l ++ ": Missing field name"
          hs  -> throwError $ show l ++ ": Bad field name " ++ show h
      _ -> throwError $ show l ++ ": Missing ':' for field " ++ show (ltrim s)

-- | Collect 'Header' and subsequent 'Content's into 'GenericEntry'.
--
--   Tailing 'Content's?  That's an error.
--
groupLines :: [GenericLine] -> P GenericFile
groupLines [] = pure []
groupLines (Content l c : _) = throwError $ show l ++ ": Missing field"
groupLines (Header _ h : ls) = (GenericEntry h [ c | Content _ c <- cs ] :) <$> groupLines ls1
  where
    (cs, ls1) = span isContent ls
    isContent Content{} = True
    isContent Header{} = False

-- | Remove leading whitespace and line comment.
trimLineComment :: String -> String
trimLineComment = stripComments . ltrim

-- | Break a comma-separated string.  Result strings are @trim@med.
splitCommas :: String -> [String]
splitCommas s = words $ map (\c -> if c == ',' then ' ' else c) s

-- | ...and trailing, but not leading, whitespace.
stripComments :: String -> String
stripComments "" = ""
stripComments ('-':'-':c:_) | isSpace c = ""
stripComments (c : s) = cons c (stripComments s)
  where
    cons c "" | isSpace c = ""
    cons c s = c : s
