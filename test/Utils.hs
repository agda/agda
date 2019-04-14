{-# LANGUAGE CPP               #-}
{-# LANGUAGE OverloadedStrings #-}

module Utils where

import Data.Ord
import Data.Text (Text)
import qualified Data.Text as T
import System.Exit

import Control.Applicative
import System.Environment
import Data.Maybe
import Data.Char
import qualified Data.Set as S
import Test.Tasty.Silver
import Test.Tasty.Silver.Advanced (readFileMaybe)
import Data.List
import System.FilePath
import qualified System.FilePath.Find as Find
import System.FilePath.GlobPattern
import System.Directory
import System.PosixCompat.Time (epochTime)
import System.PosixCompat.Files (modificationTime)

import qualified Data.ByteString as BS

import Data.Text.Encoding
import qualified System.Process.Text as PT
import Data.Array
import qualified Text.Regex.TDFA as R
import qualified Text.Regex.TDFA.Text as RT (compile)

type ProgramResult = (ExitCode, T.Text, T.Text)

type AgdaArgs = [String]


readAgdaProcessWithExitCode :: AgdaArgs -> T.Text -> IO (ExitCode, T.Text, T.Text)
readAgdaProcessWithExitCode args inp = do
  agdaBin <- getAgdaBin
  envArgs <- getEnvAgdaArgs
  PT.readProcessWithExitCode agdaBin (envArgs ++ args) inp

getEnvAgdaArgs :: IO AgdaArgs
getEnvAgdaArgs = maybe [] words <$> getEnvVar "AGDA_ARGS"

getAgdaBin :: IO FilePath
getAgdaBin = do
  agda <- getEnvVar "AGDA_BIN"
  case agda of
    Just x -> return x
    Nothing -> fail "AGDA_BIN environment variable not set, aborting..."

-- | Gets the program executable. If an environment variable
-- YYY_BIN is defined (with yyy converted to upper case),
-- the value of it is returned. Otherwise, the input value
-- is returned unchanged.
getProg :: String -> IO FilePath
getProg prog = fromMaybe prog <$> getEnvVar (map toUpper prog ++ "_BIN")

getEnvVar :: String -> IO (Maybe String)
getEnvVar v =
  lookup v <$> getEnvironment

-- | Checks if a String has Agda extension
hasAgdaExtension :: FilePath -> Bool
hasAgdaExtension = isJust . dropAgdaExtension'

data SearchMode = Rec | NonRec deriving (Eq)

dropAgdaExtension' :: FilePath -> Maybe FilePath
dropAgdaExtension' p =  stripExtension ".agda" p
                        <|> stripExtension ".lagda" p
                        <|> stripExtension ".lagda.tex" p
                        <|> stripExtension ".lagda.rst" p
                        <|> stripExtension ".lagda.md" p
                        <|> stripExtension ".lagda.org" p
#if !MIN_VERSION_filepath(1,4,1)
  where
    stripExtension :: String -> FilePath -> Maybe FilePath
    stripExtension e = fmap reverse . stripPrefix (reverse e) . reverse
#endif

dropAgdaExtension :: FilePath -> FilePath
dropAgdaExtension p =
  fromMaybe (error$ "Utils.hs: Path " ++ p ++ " does not have an Agda extension") $
  dropAgdaExtension' p

dropAgdaOrOtherExtension :: FilePath -> FilePath
dropAgdaOrOtherExtension = fromMaybe <$> dropExtension <*> dropAgdaExtension'

-- | Find (non)recursively all Agda files in the given directory
--   and order them alphabetically, with the exception that
--   the ones from the last week come first, ordered by age (youngest first).
--   This heuristic should run the interesting tests first.
getAgdaFilesInDir :: SearchMode -> FilePath -> IO [FilePath]
getAgdaFilesInDir recurse dir = do
  now <- epochTime
  -- Andreas, 2017-04-29 issue #2546
  -- We take first the new test cases, then the rest.
  -- Both groups are ordered alphabetically,
  -- but for the first group, the younger ones come first.
  let order :: Find.FileInfo -> Find.FileInfo -> Ordering
      order = comparing $ \ info ->
        let age = now - modificationTime (Find.infoStatus info) in
        -- Building a tuple for lexicographic comparison:
        ( Down $  -- This Down reverses the usual order Nothing < Just
            if age > consideredNew then Nothing else Just $
              Down age -- This Down reverses the effect of the first Down
        , Find.infoPath info
        )
      -- Test cases from up to one week ago are considered new.
      consideredNew = 7 * 24 * 60 * 60
      -- If @recurse /= Rec@ don't go into subdirectories
      recP = pure (recurse == Rec) Find.||? Find.depth Find.<? 1
  map Find.infoPath  . sortBy order <$>
    findWithInfo recP (hasAgdaExtension <$> Find.filePath) dir


-- | Search a directory recursively, with recursion controlled by a
--   'RecursionPredicate'.  Lazily return a unsorted list of all files
--   matching the given 'FilterPredicate'.  Any errors that occur are
--   ignored, with warnings printed to 'stderr'.
findWithInfo
  :: Find.RecursionPredicate  -- ^ Control recursion into subdirectories.
  -> Find.FilterPredicate     -- ^ Decide whether a file appears in the result.
  -> FilePath                 -- ^ Directory to start searching.
  -> IO [Find.FileInfo]       -- ^ Files that matched the 'FilterPredicate'.
findWithInfo recurse filt dir = Find.fold recurse act [] dir
  where
  -- Add file to list front when it matches the filter
  act :: [Find.FileInfo] -> Find.FileInfo -> [Find.FileInfo]
  act fs f
    | Find.evalClause filt f = f:fs
    | otherwise = fs

-- | An Agda file path as test name
asTestName :: FilePath -> FilePath -> String
asTestName testDir path = intercalate "-" parts
  where parts = splitDirectories $ dropAgdaExtension $ makeRelative testDir path

doesEnvContain :: String -> IO Bool
doesEnvContain v = isJust <$> getEnvVar v

readTextFileMaybe :: FilePath -> IO (Maybe Text)
readTextFileMaybe f = fmap decodeUtf8 <$> readFileMaybe f

writeTextFile :: FilePath -> Text -> IO ()
writeTextFile f = BS.writeFile f . encodeUtf8

-- | Replaces all matches of a regex with the given text.
--
-- (There doesn't seem to be any such function in the regex-tdfa libraries?)
replace :: R.Regex -> T.Text -> T.Text -> T.Text
replace rgx new inp =
  foldr repl inp matches
  where
    -- the matches are in ascending, non-overlapping order. We take advantage
    -- of this by replacing the matches in last-to-first order,
    -- which means we don't have to worry about changing offsets.
    matches = R.matchAll rgx inp
    repl :: R.MatchArray -> T.Text -> T.Text
    repl match t =
      T.take off t `T.append` new `T.append` T.drop (off + len) t
      where
        (off, len) = match ! 0

mkRegex :: T.Text -> R.Regex
mkRegex r = either (error "Invalid regex") id $
  RT.compile R.defaultCompOpt R.defaultExecOpt r

cleanOutput :: T.Text -> IO T.Text
cleanOutput inp = do
  pwd <- getCurrentDirectory

  return $ clean' pwd inp
  where
    clean' pwd t = foldl (\t' (rgx,n) -> replace rgx n t') t rgxs
      where
        rgxs = map (\(r, x) -> (mkRegex r, x))
          [ ("[^ (]*test.Fail.", "")
          , ("[^ (]*test.Succeed.", "")
          , ("[^ (]*test.Common.", "")
          , (T.pack pwd `T.append` ".test", "..")
          , ("\\\\", "/")
          , (":[[:digit:]]+:$", "")
          , ("[^ (]*lib.prim", "agda-default-include-path")
          , ("\xe2\x80\x9b|\xe2\x80\x99|\xe2\x80\x98|`", "'")
          ]

doesCommandExist :: String -> IO Bool
doesCommandExist cmd = isJust <$> findExecutable cmd
