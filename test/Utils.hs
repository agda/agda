
module Utils (module Utils,
              AgdaError(..)) where

import Control.Applicative
import Control.Arrow ((&&&))
import Control.Monad

import Data.Array
import Data.Bifunctor (first)
import qualified Data.ByteString as BS
import Data.Char
import Data.List
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Ord
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
import System.Process (proc, CreateProcess(..) )
import qualified System.Process.Text as PT

import Test.Tasty.Silver
import Test.Tasty.Silver.Advanced (readFileMaybe)

import qualified Text.Regex.TDFA as R
import qualified Text.Regex.TDFA.Text as RT ( compile )

import Agda.Interaction.ExitCode (AgdaError(..), agdaErrorFromInt)
import Agda.Utils.Maybe
import Agda.Utils.Environment

data ProgramResult = ProgramResult
  { exitCode :: ExitCode
  , stdOut   :: Text
  , stdErr   :: Text
  } deriving (Read, Show, Eq)

fromProgramResult :: ProgramResult -> (ExitCode, Text, Text)
fromProgramResult (ProgramResult c o e) = (c, o, e)

toProgramResult :: (ExitCode, Text, Text) -> ProgramResult
toProgramResult (c, o, e) = ProgramResult c o e

printProgramResult :: ProgramResult -> Text
printProgramResult = printProcResult . fromProgramResult

type AgdaArgs = [String]


readAgdaProcessWithExitCode :: AgdaArgs -> Text
                            -> IO (ExitCode, Text, Text)
readAgdaProcessWithExitCode args inp = do
  agdaBin <- getAgdaBin
  envArgs <- getEnvAgdaArgs
  let agdaProc = (proc agdaBin (envArgs ++ args)) { create_group = True }
  PT.readCreateProcessWithExitCode agdaProc inp

data AgdaResult
  = AgdaSuccess (Maybe Text)          -- ^ A success can come with warnings
  | AgdaFailure Int (Maybe AgdaError) -- ^ A failure, with exit code

runAgdaWithOptions
  :: String         -- ^ test name
  -> AgdaArgs       -- ^ options (including the name of the input file)
  -> Maybe FilePath -- ^ file containing additional options and flags
  -> Maybe FilePath -- ^ file containing additional environment variables
  -> IO (ProgramResult, AgdaResult)
runAgdaWithOptions testName opts mflag mvars = do
  flags <- case mflag of
    Nothing       -> pure []
    Just flagFile -> maybe [] T.unpack <$> readTextFileMaybe flagFile

  -- setting the additional environment variables, saving a backup
  backup <- case mvars of
    Nothing      -> pure []
    Just varFile -> do
      addEnv <- maybe [] T.lines <$> readTextFileMaybe varFile
      backup <- if addEnv /= [] then getEnvironment else pure []
      forM_ addEnv $ \ assgnmt -> do
        let (var, eqval) = T.break (== '=') assgnmt
        let val = T.unpack $ T.drop 1 eqval
        val <- expandEnvironmentVariables val
        setEnv (T.unpack var) val
      pure backup

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

  -- reinstating the old environment
  mapM_ (uncurry setEnv) backup

  cleanedStdOut <- cleanOutput stdOut
  cleanedStdErr <- cleanOutput stdErr
  let res = ProgramResult ret cleanedStdOut cleanedStdErr
  pure $ (res,) $ case ret of
    ExitSuccess      -> AgdaSuccess $ filterMaybe hasWarning cleanedStdOut
    ExitFailure code -> AgdaFailure code (agdaErrorFromInt code)

hasWarning :: Text -> Bool
hasWarning t =
 "———— All done; warnings encountered ————————————————————————"
 `T.isInfixOf` t


getEnvAgdaArgs :: IO AgdaArgs
getEnvAgdaArgs = maybe [] words <$> getEnvVar "AGDA_ARGS"

getAgdaBin :: IO FilePath
getAgdaBin = fromMaybeM err $ getEnvVar "AGDA_BIN"
  where
  err = fail "AGDA_BIN environment variable not set, aborting..."

-- | Gets the program executable. If an environment variable
-- YYY_BIN is defined (with yyy converted to upper case),
-- the value of it is returned. Otherwise, the input value
-- is returned unchanged.
getProg :: String -> IO FilePath
getProg prog = fromMaybe prog <$> getEnvVar (map toUpper prog ++ "_BIN")

getEnvVar :: String -> IO (Maybe String)
getEnvVar v =
  lookup v <$> getEnvironment

-- | List of possible extensions of agda files.
agdaExtensions :: [String]
agdaExtensions =
  [ ".agda"
  , ".lagda"
  , ".lagda.tex"
  , ".lagda.rst"
  , ".lagda.md"
  , ".lagda.org"
  ]

-- | List of files paired with agda files by the test suites.
-- E.g. files recording the accepted output or error message.
helperExtensions :: [String]
helperExtensions =
  [ ".flags"        -- Supplementary file
  , ".warn"         -- Produced by test/Succeed
  , ".err"          -- Produced by test/Fail
  , ".in", ".out"   -- For running test/interaction
  ]

-- | Generalizes 'stripExtension'.
stripAnyOfExtensions :: [String] -> FilePath -> Maybe FilePath
stripAnyOfExtensions exts p = listToMaybe $ catMaybes $ map (`stripExtension` p) exts

stripAgdaExtension :: FilePath -> Maybe FilePath
stripAgdaExtension = stripAnyOfExtensions agdaExtensions

stripHelperExtension :: FilePath -> Maybe FilePath
stripHelperExtension = stripAnyOfExtensions helperExtensions

-- | Checks if a String has Agda extension
hasAgdaExtension :: FilePath -> Bool
hasAgdaExtension = isJust . stripAgdaExtension

dropAgdaExtension :: FilePath -> FilePath
dropAgdaExtension p =
  fromMaybe (error $ "Utils.hs: Path " ++ p ++ " does not have an Agda extension") $
  stripAgdaExtension p

dropAgdaOrOtherExtension :: FilePath -> FilePath
dropAgdaOrOtherExtension = fromMaybe <$> dropExtension <*> stripAgdaExtension

data SearchMode = Rec | NonRec deriving (Eq)

-- | Find (non)recursively all Agda files in the given directory
--   and order them alphabetically, with the exception that
--   the ones from the last week come first, ordered by age (youngest first).
--   This heuristic should run the interesting tests first.
--   The age computation also considers helper file modification time
--   (.err, .in, .out, .warn).
getAgdaFilesInDir :: SearchMode -> FilePath -> IO [FilePath]
getAgdaFilesInDir recurse dir = do
  -- Get all agda files...
  agdaFiles <- findWithInfo recP (hasAgdaExtension <$> Find.filePath) dir
  -- ...and organize them in a map @baseName ↦ (modificationTime, baseName.ext)@.
  -- We may assume that all agda files have different @baseName@s.
  -- (Otherwise agda will complain when trying to load them.)
  let m = Map.fromList $ flip map agdaFiles $
            {-key-} (dropAgdaExtension . Find.infoPath) &&&
            {-val-} (modificationTime . Find.infoStatus) &&& Find.infoPath
  -- Andreas, 2020-06-08, issue #4736: Go again through all the files.
  -- If we find one whose baseName is in the map and
  -- that has a newer modificationTime than what is stored in the map,
  -- we update the modificationTime in the map.
  m <- Find.fold recP (flip updateModificationTime) m dir
  -- Andreas, 2017-04-29 issue #2546
  -- We take first the new test cases, then the rest.
  -- Both groups are ordered alphabetically,
  -- but for the first group, the younger ones come first.
  -- Ignore first (i.e., the time) component if older than @consideredNew@.
  -- The second component is the filepath.
  now <- epochTime
  let order = comparing $ first $ \ t -> let age = now - t in
        Down $  -- This Down reverses the usual order Nothing < Just
          if age > consideredNew then Nothing else Just $
            Down age -- This Down reverses the effect of the first Down
  return $ map snd $ sortBy order $ Map.elems m
  where
  -- If @recurse /= Rec@ don't go into subdirectories
  recP = pure (recurse == Rec) Find.||? Find.depth Find.<? 1
  -- Updating the map of agda files to take modification
  -- of secondary files (.err, .in, .out) into account.
  updateModificationTime f =
    case stripHelperExtension $ Find.infoPath f of
      Just k  -> Map.adjust (updIfNewer $ modificationTime $ Find.infoStatus f) k
      Nothing -> id
  updIfNewer tNew old@(tOld, f)
    | tNew > tOld = (tNew, f)
    | otherwise   = old
  -- Test cases from up to one week ago are considered new.
  consideredNew = 7 * 24 * 60 * 60

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
  act = flip $ consIf $ Find.evalClause filt

-- | Prepend element if it satisfies the given condition.
consIf :: (a -> Bool) -> a -> [a] -> [a]
consIf p a = if p a then (a :) else id

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
replace :: R.Regex -> Text -> Text -> Text
replace rgx new inp =
  foldr repl inp matches
  where
    -- the matches are in ascending, non-overlapping order. We take advantage
    -- of this by replacing the matches in last-to-first order,
    -- which means we don't have to worry about changing offsets.

    matches = R.matchAll rgx inp

    repl :: R.MatchArray -> Text -> Text
    repl match t =
      T.take off t `T.append` new `T.append` T.drop (off + len) t
      where
        (off, len) = match ! 0

mkRegex :: Text -> R.Regex
mkRegex r = either (error "Invalid regex") id $
  RT.compile R.defaultCompOpt R.defaultExecOpt r

cleanOutput :: Text -> IO Text
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
