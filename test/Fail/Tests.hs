{-# LANGUAGE CPP #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE OverloadedStrings #-}
module Fail.Tests where

import Test.Tasty
import Test.Tasty.Silver
import Test.Tasty.Silver.Advanced (readFileMaybe, goldenTest1, GDiff (..), GShow (..))
import Data.Maybe
import System.FilePath
import qualified Data.Text as T
import Data.Text.Encoding
import System.Exit
import System.Directory
import qualified Data.ByteString as BS

#if __GLASGOW_HASKELL__ <= 708
import Control.Applicative ((<$>))
#endif

import qualified Text.Regex.TDFA.Text as RT
import qualified Text.Regex.TDFA as R

import Utils


testDir :: FilePath
testDir = "test" </> "Fail"

tests :: IO TestTree
tests = do
  inpFiles <- getAgdaFilesInDir NonRec testDir

  let tests' = map mkFailTest inpFiles

  return $ testGroup "Fail" tests'

data AgdaResult
  = AgdaResult T.Text -- the cleaned stdout
  | AgdaUnexpectedSuccess ProgramResult



mkFailTest :: FilePath -- inp file
    -> TestTree
mkFailTest inp = do
  goldenTest1 testName readGolden (printAgdaResult <$> doRun) resDiff resShow updGolden
--  goldenVsAction testName goldenFile doRun printAgdaResult
  where testName = asTestName testDir inp
        goldenFile = (dropExtension inp) <.> ".err"
        flagFile = (dropExtension inp) <.> ".flags"

        readGolden = fmap decodeUtf8 <$> readFileMaybe goldenFile
        updGolden = BS.writeFile goldenFile . encodeUtf8

        doRun = (do
          flags <- fromMaybe [] . fmap (T.unpack . decodeUtf8) <$> readFileMaybe flagFile
          let agdaArgs = ["-v0", "-i" ++ testDir, "-itest/" , inp, "--ignore-interfaces", "--no-default-libraries"] ++ words flags
          res@(ret, stdout, _) <- readAgdaProcessWithExitCode agdaArgs T.empty

          if ret == ExitSuccess
            then
              return $ AgdaUnexpectedSuccess res
            else
              AgdaResult <$> clean stdout
          )

mkRegex :: T.Text -> R.Regex
mkRegex r = either (error "Invalid regex") id $
  RT.compile R.defaultCompOpt R.defaultExecOpt r

-- | Treats newlines or consecutive whitespaces as one single whitespace.
--
-- Philipp20150923: On travis lines are wrapped at different positions sometimes.
-- It's not really clear to me why this happens, but just ignoring line breaks
-- for comparing the results should be fine.
resDiff :: T.Text -> T.Text -> GDiff
resDiff t1 t2 =
  if strip t1 == strip t2
    then
      Equal
    else
      DiffText Nothing t1 t2
  where
    strip = replace (mkRegex " +") " " . replace (mkRegex "(\n|\r)") " "

resShow :: T.Text -> GShow
resShow = ShowText

printAgdaResult :: AgdaResult -> T.Text
printAgdaResult (AgdaResult t) = t
printAgdaResult (AgdaUnexpectedSuccess p)= "AGDA_UNEXPECTED_SUCCESS\n\n" `T.append` printProcResult p

clean :: T.Text -> IO T.Text
clean inp = do
  pwd <- getCurrentDirectory

  return $ clean' pwd inp
  where
    clean' pwd t = foldl (\t' (rgx,n) -> replace rgx n t') t rgxs
      where
        rgxs = map (\(r, x) -> (mkRegex r, x))
          [ ("[^ (]*test.Fail.", "")
          , ("[^ (]*test.Common.", "")
          , (T.pack pwd `T.append` ".test", "..")
          , ("\\\\", "/")
          , (":[[:digit:]]\\+:$", "")
          , ("[^ (]*lib.prim", "agda-default-include-path")
          , ("\xe2\x80\x9b|\xe2\x80\x99|\xe2\x80\x98|`", "'")
          ]

