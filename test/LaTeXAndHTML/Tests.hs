{-# LANGUAGE DoAndIfThenElse   #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}

module LaTeXAndHTML.Tests where

import Control.Monad
import Data.Char
import qualified Data.List as List
import Data.Maybe
import Data.Text.Encoding
import qualified Data.ByteString as BS

import qualified Network.URI.Encode
import System.Directory
import System.Exit
import System.FilePath
import System.IO.Temp
import System.Process
import qualified System.Process.Text as PT
import qualified System.Process.ByteString as PB
import qualified Data.Text as T

import Test.Tasty
import Test.Tasty.Silver
import Test.Tasty.Silver.Advanced (readFileMaybe)
import Test.Tasty.Silver.Filter

import Utils

import Agda.Utils.Three

type LaTeXProg = String

allLaTeXProgs :: [LaTeXProg]
allLaTeXProgs = ["pdflatex", "xelatex", "lualatex"]

testDir :: FilePath
testDir = "test" </> "LaTeXAndHTML" </> "succeed"

disabledTests :: [RegexFilter]
disabledTests =
  [ -- Issue #3170
    RFInclude "UnicodeDeclare_LaTeX"
  , RFInclude "UnicodeDeclare_QuickLaTeX"
  ]

-- | List of test groups with names
--
-- @
--   [ "LaTeXAndHTML" , "HTMLOnly" , "LaTeXOnly" , "QuickLaTeXOnly" ]
-- @.
--
tests :: IO [TestTree]
tests = do
  allTests <- taggedListOfAllTests
  let (html, latex, quicklatex) = (\ f -> partition3 (f . fst) allTests) $ \case
        HTML       -> One
        LaTeX      -> Two
        QuickLaTeX -> Three
  return
    [ testGroup "LaTeXAndHTML"   $ map snd allTests
    , testGroup "HTMLOnly"       $ map snd html
    , testGroup "LaTeXOnly"      $ map snd latex
    , testGroup "QuickLaTeXOnly" $ map snd quicklatex
    ]

taggedListOfAllTests :: IO [(Kind, TestTree)]
taggedListOfAllTests = do
  inpFiles <- getAgdaFilesInDir NonRec testDir
  agdaBin  <- getAgdaBin
  return $
    [ (k, mkLaTeXOrHTMLTest k agdaBin f)
    | f <- inpFiles
    -- Note that the LaTeX backends are only tested on the @.lagda@
    -- and @.lagda.tex@ files.
    , k <- HTML : concat [ [ LaTeX, QuickLaTeX ]
                         | any (`List.isSuffixOf` takeExtensions f)
                               [".lagda",".lagda.tex"]
                         ]
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
  -> FilePath -- ^ Agda binary.
  -> FilePath -- ^ Input file.
  -> TestTree
mkLaTeXOrHTMLTest k agdaBin inp =
  goldenVsAction
    testName
    goldenFile
    (liftM2 (,) getCurrentDirectory doRun)
    (uncurry printLaTeXResult)
  where
  extension = case k of
    LaTeX      -> "tex"
    QuickLaTeX -> "quick.tex"
    HTML       -> "html"

  flags :: FilePath -> [String]
  flags dir = case k of
    LaTeX      -> latexFlags
    QuickLaTeX -> latexFlags ++ ["--only-scope-checking"]
    HTML       -> ["--html", "--html-dir=" ++ dir]
    where
    latexFlags = ["--latex", "--latex-dir=" ++ dir]

  testName    = asTestName testDir inp ++ "_" ++ show k
  flagFile    = dropAgdaExtension inp <.> "flags"
  goldenFile  = dropAgdaExtension inp <.> extension
  -- For removing a LaTeX compiler when testing @Foo.lagda@, you can
  -- create a file @Foo.compile@ with the list of the LaTeX compilers
  -- that you want to use (e.g. ["xelatex", "lualatex"]).
  compFile    = dropAgdaExtension inp <.> ".compile"
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
    let agdaArgs = flags outDir ++
                   [ "-i" ++ testDir
                   , inp
                   , "--ignore-interfaces"
                   , "--no-libraries"
                   ] ++ extraFlags
    res@(ret, _, _) <- PT.readProcessWithExitCode agdaBin agdaArgs T.empty
    if ret /= ExitSuccess then
      return $ AgdaFailed res
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
                       mangle (printProcResult p)
  LaTeXFailed progs -> "LATEX_COMPILE_FAILED with "
                         `T.append`
                       T.intercalate ", " (map T.pack progs)
  where
  -- Tries to make the resulting string more platform-independent.
  mangle        = T.unwords . T.words . removeCWD
  removeCWD
    | null dir  = id
    | otherwise = T.concat . T.splitOn (T.pack dir)

readMaybe :: Read a => String -> Maybe a
readMaybe s =
  case reads s of
    [(x, rest)] | all isSpace rest -> Just x
    _                              -> Nothing
