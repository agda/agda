{-# LANGUAGE CPP               #-}
{-# LANGUAGE DoAndIfThenElse   #-}
{-# LANGUAGE OverloadedStrings #-}

module LaTeXAndHTML.Tests where

import Test.Tasty
import Test.Tasty.Silver
import Test.Tasty.Silver.Advanced (readFileMaybe)
import Data.Char
import Data.List
import Data.Maybe
import System.Exit
import System.FilePath
import System.Process
import qualified System.Process.Text as PT
import qualified System.Process.ByteString as PB
import qualified Data.Text as T
import System.IO.Temp
import Data.Text.Encoding
import qualified Data.ByteString as BS

#if __GLASGOW_HASKELL__ <= 708
import Control.Applicative ((<$>))
#endif

import Utils


type LaTeXProg = String

allLaTeXProgs :: [LaTeXProg]
allLaTeXProgs = ["pdflatex", "xelatex", "lualatex"]

testDir :: FilePath
testDir = "test" </> "LaTeXAndHTML" </> "succeed"

tests :: IO TestTree
tests = do
  inpFiles <- getAgdaFilesInDir NonRec testDir
  agdaBin  <- getAgdaBin
  return $ testGroup "LaTeXAndHTML"
    [ mkLaTeXOrHTMLTest k agdaBin f
    | f <- inpFiles
    , k <- HTML : [ LaTeX | any (`isSuffixOf` takeExtensions f) [".lagda",".lagda.tex"] ]
    ]

data LaTeXResult
  = AgdaFailed ProgramResult
  | LaTeXFailed LaTeXProg ProgramResult
  | Success T.Text -- ^ The resulting LaTeX or HTML file.

data Kind = LaTeX | HTML
  deriving Show

mkLaTeXOrHTMLTest
  :: Kind
  -> FilePath -- ^ Agda binary.
  -> FilePath -- ^ Input file.
  -> TestTree
mkLaTeXOrHTMLTest k agdaBin inp =
  goldenVsAction testName goldenFile doRun printLaTeXResult
  where
  extension = case k of
    LaTeX -> "tex"
    HTML  -> "html"

  flag = case k of
    LaTeX -> "latex"
    HTML  -> "html"

  testName    = asTestName testDir inp ++ "_" ++ show k
  goldenFile  = dropAgdaExtension inp <.> extension
  compFile    = dropAgdaExtension inp <.> ".compile"
  outFileName = takeFileName goldenFile

  doRun = withTempDirectory "." testName $ \outDir -> do
    let agdaArgs = [ "--" ++ flag
                   , "-i" ++ testDir
                   , inp
                   , "--ignore-interfaces"
                   , "--" ++ flag ++ "-dir=" ++ outDir
                   ]
    res@(ret, _, _) <- PT.readProcessWithExitCode agdaBin agdaArgs T.empty
    if ret /= ExitSuccess then
      return $ AgdaFailed res
    else do
      output <- decodeUtf8 <$> BS.readFile (outDir </> outFileName)
      let done = return $ Success output
      case k of
        HTML  -> done
        LaTeX -> do
          -- read compile options
          doCompile <- readFileMaybe compFile
          case doCompile of
            -- there is no compile file, so we are finished
            Nothing -> done
            -- there is a compile file, check it's content
            Just content -> do
              let latexProgs =
                    fromMaybe allLaTeXProgs
                      (readMaybe $ T.unpack $ decodeUtf8 content)
              -- run all latex compilers
              rl <- doesEnvContain "DONT_RUN_LATEX"
              if rl
                then done
                else
                  foldl (runLaTeX outFileName outDir) done latexProgs

  runLaTeX :: FilePath -- tex file
      -> FilePath -- working dir
      -> IO LaTeXResult -- continuation
      -> LaTeXProg
      -> IO LaTeXResult
  runLaTeX texFile wd cont prog = do
      let proc' = (proc prog ["-interaction=errorstopmode", texFile]) { cwd = Just wd }
      (ret, out, err) <- PB.readCreateProcessWithExitCode proc' BS.empty
      if ret == ExitSuccess then
        cont
      else do
        let dec = decodeUtf8With (\_ _ -> Just '?')
            res = (ret, dec out, dec err)
        return $ LaTeXFailed prog res

printLaTeXResult :: LaTeXResult -> T.Text
printLaTeXResult (Success t)          = t
printLaTeXResult (AgdaFailed p)       = "AGDA_COMPILE_FAILED\n\n" `T.append` printProcResult p
printLaTeXResult (LaTeXFailed prog p) = "LATEX_COMPILE_FAILED with "
    `T.append` (T.pack prog)
    `T.append` "\n\n"
    `T.append` printProcResult p

readMaybe :: Read a => String -> Maybe a
readMaybe s =
  case reads s of
    [(x, rest)] | all isSpace rest -> Just x
    _                              -> Nothing
