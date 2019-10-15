
module Utils where

import Control.Applicative

import Data.Array
import Data.Bifunctor (first)
import qualified Data.ByteString as BS
import Data.Char
import Data.List
import Data.Maybe
import Data.Ord
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as T
import Data.Text.Encoding

import System.Directory
import System.Environment
import System.Exit
import System.FilePath
import qualified System.FilePath.Find as Find
import System.FilePath.GlobPattern
import System.IO.Temp
import System.PosixCompat.Time (epochTime)
import System.PosixCompat.Files (modificationTime)
import qualified System.Process.Text as PT

import Test.Tasty.Silver
import Test.Tasty.Silver.Advanced (readFileMaybe)

import qualified Text.Regex.TDFA as R
import qualified Text.Regex.TDFA.String as R

import Agda.Utils.Maybe

data ProgramResult = ProgramResult
  { exitCode :: ExitCode
  , stdOut   :: T.Text
  , stdErr   :: T.Text
  } deriving (Read, Show, Eq)

fromProgramResult :: ProgramResult -> (ExitCode, T.Text, T.Text)
fromProgramResult (ProgramResult c o e) = (c, o, e)

toProgramResult :: (ExitCode, T.Text, T.Text) -> ProgramResult
toProgramResult (c, o, e) = ProgramResult c o e

printProgramResult :: ProgramResult -> T.Text
printProgramResult = printProcResult . fromProgramResult

type AgdaArgs = [String]


readAgdaProcessWithExitCode :: AgdaArgs -> T.Text
                            -> IO (ExitCode, T.Text, T.Text)
readAgdaProcessWithExitCode args inp = do
  agdaBin <- getAgdaBin
  envArgs <- getEnvAgdaArgs
  PT.readProcessWithExitCode agdaBin (envArgs ++ args) inp

data AgdaResult
  = AgdaSuccess (Maybe T.Text) -- A success can come with warnings
  | AgdaFailure                -- A failure

runAgdaWithOptions
  :: String         -- ^ test name
  -> AgdaArgs       -- ^ options (including the name of the input file)
  -> Maybe FilePath -- ^ file containing additional options and flags
  -> IO (ProgramResult, AgdaResult)
runAgdaWithOptions testName opts mflag = do
  flags <- case mflag of
    Nothing       -> pure []
    Just flagFile -> maybe [] T.unpack <$> readTextFileMaybe flagFile
  let agdaArgs = opts ++ words flags
  let runAgda  = \ extraArgs -> let args = agdaArgs ++ extraArgs in
                                readAgdaProcessWithExitCode args T.empty
  (ret, stdOut, stdErr) <-
    if "--compile" `elem` agdaArgs
      -- Andreas, 2017-04-14, issue #2317
      -- Create temporary files in system temp directory.
      -- This has the advantage that upon Ctrl-C no junk is left behind
      -- in the Agda directory.
    then withSystemTempDirectory ("MAZ_compile_" ++ testName)
           (\ compDir -> runAgda ["--compile-dir=" ++ compDir])
    else runAgda []

  cleanedStdOut <- cleanOutput stdOut
  cleanedStdErr <- cleanOutput stdErr
  let res = ProgramResult ret cleanedStdOut cleanedStdErr
  pure $ (res,) $ case ret of
    ExitSuccess -> AgdaSuccess $ filterMaybe hasWarning cleanedStdOut
    _           -> AgdaFailure

hasWarning :: T.Text -> Bool
hasWarning t =
 "———— All done; warnings encountered ————————————————————————"
 `T.isInfixOf` t


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

readTextFile :: FilePath -> IO Text
readTextFile f = decodeUtf8 <$> BS.readFile f

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

    -- ASR (2019-10-13). We could avoid the use of T.unpack after the
    -- fix of https://github.com/ChrisKuklewicz/regex-tdfa/issues/5.
    matches = R.matchAll rgx $ T.unpack inp

    repl :: R.MatchArray -> T.Text -> T.Text
    repl match t =
      T.take off t `T.append` new `T.append` T.drop (off + len) t
      where
        (off, len) = match ! 0

-- ASR (2019-10-13). We could avoid the use of T.unpack after the fix
-- of https://github.com/ChrisKuklewicz/regex-tdfa/issues/5.
mkRegex :: T.Text -> R.Regex
mkRegex r = either (error "Invalid regex") id $
  R.compile R.defaultCompOpt R.defaultExecOpt $ T.unpack r

cleanOutput :: T.Text -> IO T.Text
cleanOutput inp = do
  pwd <- getCurrentDirectory

  return $ clean' pwd inp
  where
    clean' pwd t = foldl (\ t' (rgx, n) -> replace rgx n t') t rgxs
      where
        rgxs = map (first mkRegex)
          [ ("[^ (]*test.Fail.", "")
          , ("[^ (]*test.Succeed.", "")
          , ("[^ (]*test.Common.", "")
          , ("[^ (]*test.Bugs.", "")
          , ("[^ (]*test.LibSucceed.", "")
          , (T.pack pwd `T.append` ".test", "..")
          , ("\\\\", "/")
          , (":[[:digit:]]+:$", "")
          , ("\\.hs:[[:digit:]]+", ".hs")
          , ("[^ (]*lib.prim", "agda-default-include-path")
          , ("\xe2\x80\x9b|\xe2\x80\x99|\xe2\x80\x98|`", "'")
          ]

doesCommandExist :: String -> IO Bool
doesCommandExist cmd = isJust <$> findExecutable cmd
