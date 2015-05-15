{-# LANGUAGE CPP #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE OverloadedStrings #-}
module LatexBackend.Tests where

import Test.Tasty
import Test.Tasty.Silver
import Test.Tasty.Silver.Advanced (readFileMaybe)
import Data.Char
import Data.Maybe
import System.Exit
import System.FilePath
import System.Process
import qualified System.Process.Text as PT
import qualified Data.Text as T
import System.IO.Temp
import Data.Text.Encoding
import qualified Data.ByteString as BS

#if __GLASGOW_HASKELL__ <= 708
import Control.Applicative ((<$>))
#endif

import Utils


type LatexProg = String

allLatexProgs :: [LatexProg]
allLatexProgs = ["pdflatex", "xelatex", "lualatex"]

testDir :: FilePath
testDir = "test" </> "LatexBackend" </> "succeed"

tests :: IO TestTree
tests = do
  inpFiles <- getAgdaFilesInDir testDir
  agdaBin <- getAgdaBin

  let tests' = map (mkLatexTest agdaBin) inpFiles

  return $ testGroup "LatexBackend" tests'

data LatexResult
  = AgdaFailed ProgramResult
  | LatexFailed LatexProg ProgramResult
  | Success T.Text -- the resulting tex file

mkLatexTest :: FilePath -- agda binary
    -> FilePath -- inp file
    -> TestTree
mkLatexTest agdaBin inp = do
  goldenVsAction testName goldenFile doRun printLatexResult
  where testName = dropExtension $ takeFileName inp
        goldenFile = (dropExtension inp) <.> ".tex"
        compFile = (dropExtension inp) <.> ".compile"
        outFileName = takeFileName goldenFile

        doRun = withTempDirectory "." testName (\outDir -> do

          let agdaArgs = ["--latex", "-i" ++ testDir, inp, "--ignore-interfaces", "--latex-dir=" ++ outDir]
          res@(ret, _, _) <- PT.readProcessWithExitCode agdaBin agdaArgs T.empty
          if ret /= ExitSuccess then
            return $ AgdaFailed res
          else do
            let outFile = outDir </> outFileName
            texOut <- decodeUtf8 <$> BS.readFile outFile

            -- read compile options
            doCompile <- readFileMaybe compFile
            case doCompile of
              -- there is no compile file, so we are finished
              Nothing -> return $ Success texOut
              -- there is a compile file, check it's content
              Just content -> do
                let latexProgs = fromMaybe allLatexProgs (readMaybe $ T.unpack $ decodeUtf8 content)
                -- run all latex compilers
                foldl (runLatex outFileName outDir) (return $ Success texOut) latexProgs
          )

        runLatex :: FilePath -- tex file
            -> FilePath -- working dir
            -> (IO LatexResult) -- continuation
            -> LatexProg
            -> IO LatexResult
        runLatex texFile wd cont prog = do
            let proc' = (proc prog ["-interaction=batchmode", texFile]) { cwd = Just wd }
#if MIN_VERSION_process_extras(0,3,0)
            res@(ret, _, _) <- PT.readCreateProcessWithExitCode proc' T.empty
#else
            (_, _, _, pHandle) <- createProcess proc'
            ret <- waitForProcess pHandle
            let res = (ret, T.empty, T.empty)
#endif
            if ret == ExitSuccess then
              cont
            else
              return $ LatexFailed prog res

printLatexResult :: LatexResult -> T.Text
printLatexResult (Success t) = t
printLatexResult (AgdaFailed p)= "AGDA_COMPILE_FAILED\n\n" `T.append` printProcResult p
printLatexResult (LatexFailed prog p) = "LATEX_COMPILE_FAILED with "
    `T.append` (T.pack prog)
    `T.append` "\n\n"
    `T.append` printProcResult p


readMaybe :: Read a => String -> Maybe a
readMaybe s =
  case reads s of
    [(x, rest)] | all isSpace rest -> Just x
    _                              -> Nothing

