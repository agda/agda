{-# LANGUAGE DoAndIfThenElse   #-}

module LaTeXAndHTML.Tests where

import Control.Monad
import Data.Char
import qualified Data.List as List
import Data.Maybe
import Data.Text.Encoding
import qualified Data.ByteString as BS
import qualified Data.Text as T

import qualified Network.URI.Encode
import System.Directory
import System.Environment (getEnvironment)
import System.Exit
import System.FilePath
import System.IO.Temp
import System.Process
import qualified System.Process.Text as PT
import qualified System.Process.ByteString as PB
import Text.Read (readMaybe)

import Test.Tasty
import Test.Tasty.Silver
import Test.Tasty.Silver.Advanced (readFileMaybe)
import Test.Tasty.Silver.Filter

import UserManual.Tests (examplesInUserManual)
import Utils

import Agda.Utils.Three

type LaTeXProg = String

allLaTeXProgs :: [LaTeXProg]
allLaTeXProgs = ["pdflatex", "xelatex", "lualatex"]

testDirPrefix :: FilePath -> FilePath
testDirPrefix x = "test" </> "LaTeXAndHTML" </> x

-- Andreas, 2021-01-30
-- See issue #5140 for the split into these two directories.
testDirs :: [FilePath]
testDirs = map testDirPrefix
  [ "fail"
  , "succeed"
  ]

userManualTestDir :: FilePath
userManualTestDir = testDirPrefix "user-manual"

disabledTests :: [RegexFilter]
disabledTests = []

-- | Filtering out tests using Text.ICU.

icuTests :: [RegexFilter]
icuTests = [ disable "LaTeXAndHTML/.*/Grapheme.*" ]
  where disable = RFInclude

-- | Filtering out tests using latex.

latexTests :: [RegexFilter]
latexTests = [ disable "LaTeXAndHTML/.*LaTeX/.*" ]
  where disable = RFInclude


-- | Test group with subgroups
--
-- @
--   "LaTeXAndHTML" / [ "HTML" , "LaTeX" , "QuickLaTeX" ]
-- @.
--
tests :: IO TestTree
tests = do
  agdaBin  <- getAgdaBin <$> getEnvironment
  suiteTests <- concat <$> mapM (taggedListOfAllTests agdaBin) testDirs
  let allTests = suiteTests ++ userManualTests agdaBin
  let (html, latex, quicklatex) = (\ f -> partition3 (f . fst) allTests) $ \case
        HTML       -> One
        LaTeX      -> Two
        QuickLaTeX -> Three
  return $
    testGroup "LaTeXAndHTML"
    [ testGroup "HTML"       $ map snd html
    , testGroup "LaTeX"      $ map snd latex
    , testGroup "QuickLaTeX" $ map snd quicklatex
    ]

taggedListOfAllTests :: FilePath -> FilePath -> IO [(Kind, TestTree)]
taggedListOfAllTests agdaBin testDir = do
  inpFiles <- getAgdaFilesInDir NonRec testDir
  return $
    [ (k, mkLaTeXOrHTMLTest k False agdaBin testDir f)
    | f <- inpFiles
    -- Note that the LaTeX backends are only tested on the @.lagda@
    -- and @.lagda.tex@ files.
    , k <- HTML : concat [ [ LaTeX, QuickLaTeX ]
                         | any (`List.isSuffixOf` takeExtensions f)
                               [".lagda",".lagda.tex"]
                         ]
    ]

-- See issue #3372 for the origin of these tests.
-- | These tests do not have a @.lagda[.tex]@ source.
userManualTests :: FilePath -> [(Kind, TestTree)]
userManualTests agdaBin =
    [ (k, mkLaTeXOrHTMLTest k True agdaBin userManualTestDir f)
    | f <- examplesInUserManual
    , k <- [LaTeX, QuickLaTeX]
    ]

data LaTeXResult
  = AgdaFailed ProgramResult
  | LaTeXFailed [LaTeXProg]
  | Success T.Text -- ^ The resulting LaTeX or HTML file.

data Kind = LaTeX | QuickLaTeX | HTML
  deriving Show

-- The test output may not be very informative for failing tests. One
-- can perhaps improve the user experience by switching from
-- goldenVsAction to something else (see test/Fail/Tests.hs for one
-- example).

mkLaTeXOrHTMLTest
  :: Kind
  -> Bool     -- ^ Should the file be copied to the temporary test
              --   directory before the test is run?
  -> FilePath -- ^ Agda binary.
  -> FilePath -- ^ Test directory in which input file resides.
  -> FilePath -- ^ Input file.
  -> TestTree
mkLaTeXOrHTMLTest k copy agdaBin testDir inp =
  goldenVsAction'
    testName
    goldenFile
    (liftM2 (,) getCurrentDirectory doRun)
    (uncurry printLaTeXResult)
  where
  extension = case k of
    LaTeX      -> "tex"
    QuickLaTeX -> "quick.tex"
    HTML       -> if "MdHighlight" `List.isPrefixOf` inFileName
                  then "md"
                  else if "RsTHighlight" `List.isPrefixOf` inFileName
                  then "rst"
                  else if "OrgHighlight" `List.isPrefixOf` inFileName
                  then "org"
                  else "html"

  flags :: FilePath -> [String]
  flags dir = case k of
    LaTeX      -> latexFlags
    QuickLaTeX -> latexFlags ++ ["--only-scope-checking"]
    HTML       -> ["--html", "--html-dir=" ++ dir]
    where
    latexFlags = ["--latex", "--latex-dir=" ++ dir]

  inFileName  = takeFileName inp
  testName    = asTestName testDir inp ++ "_" ++ show k
  baseName    = if copy
                then testDir </> dropAgdaExtension inFileName
                else dropAgdaExtension inp
  flagFile    = baseName <.> "flags"
  goldenFile  = baseName <.> extension
  -- For removing a LaTeX compiler when testing @Foo.lagda@, you can
  -- create a file @Foo.compile@ with the list of the LaTeX compilers
  -- that you want to use (e.g. ["xelatex", "lualatex"]).
  compFile    = baseName <.> "compile"
  outFileName = case k of
    LaTeX      -> golden
    HTML       -> Network.URI.Encode.encode golden
    QuickLaTeX -> replaceExtension (dropExtension golden) "tex"
    where
    golden = takeFileName goldenFile

  -- Andreas, 2017-04-14, issue #2317
  -- Create temporary files in system temp directory.
  -- This has the advantage that upon Ctrl-C no junk is left behind
  -- in the Agda directory.
  -- doRun = withTempDirectory "." testName $ \outDir -> do
  doRun = withSystemTempDirectory testName $ \outDir -> do
    -- One can give extra options in .flags files (one per line).
    flagFileExists <- doesFileExist flagFile
    extraFlags <- if flagFileExists
                  then lines <$> readFile flagFile
                  else return []
    let newFile  = outDir </> inFileName
        agdaArgs = flags outDir ++
                   [ "-i" ++ if copy then outDir else testDir
                   , if copy then newFile else inp
                   , "--ignore-interfaces"
                   , "--no-libraries"
                   ] ++ extraFlags
    when copy $ copyFile inp newFile
    (exitcode, out, err) <- PT.readProcessWithExitCode agdaBin agdaArgs T.empty
    if exitcode /= ExitSuccess then
      AgdaFailed <$> do
        ProgramResult exitcode
          <$> cleanOutput out
          <*> cleanOutput err
    else do
      output <- decodeUtf8 <$> BS.readFile (outDir </> outFileName)
      let done    = return $ Success output
          compile = do
            rl <- doesEnvContain "DONT_RUN_LATEX"
            if rl
            then done
            else do
              -- read compile options
              doCompile <- readFileMaybe compFile
              case doCompile of
                -- there is no compile file, so we run all the LaTeX compilers
                Nothing -> foldl (runLaTeX outFileName outDir) done allLaTeXProgs
                -- there is a compile file, check it's content
                Just content -> do
                  let latexProgs =
                        fromMaybe allLaTeXProgs
                          (readMaybe $ T.unpack $ decodeUtf8 content)
                  -- run the selected LaTeX compilers
                  foldl (runLaTeX outFileName outDir) done latexProgs
      case k of
        HTML       -> done
        LaTeX      -> compile
        QuickLaTeX -> compile

  runLaTeX :: FilePath -- tex file
      -> FilePath -- working dir
      -> IO LaTeXResult -- continuation
      -> LaTeXProg
      -> IO LaTeXResult
  runLaTeX texFile wd cont prog = do
      let proc' = (proc prog ["-interaction=errorstopmode", texFile]) { cwd = Just wd }
      (ret, _, _) <- PB.readCreateProcessWithExitCode proc' BS.empty
      if ret == ExitSuccess then
        cont
      else do
        r <- cont
        return $ case r of
          LaTeXFailed progs -> LaTeXFailed (prog : progs)
          _                 -> LaTeXFailed [prog]

printLaTeXResult
  :: FilePath     -- ^ The current working directory.
  -> LaTeXResult
  -> T.Text
printLaTeXResult dir r = case r of
  Success t         -> t
  AgdaFailed p      -> "AGDA_COMPILE_FAILED\n\n"
                         `T.append`
                       mangle (printProgramResult p)
  LaTeXFailed progs -> "LATEX_COMPILE_FAILED with "
                         `T.append`
                       T.intercalate ", " (map T.pack progs)
  where
  -- Tries to make the resulting string more platform-independent.
  mangle        = T.unwords . T.words . removeCWD
  removeCWD
    | null dir  = id
    | otherwise = T.concat . T.splitOn (T.pack dir)
