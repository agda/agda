{-# LANGUAGE CPP #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE OverloadedStrings #-}
module Fail.Tests where

import Test.Tasty
import Test.Tasty.Silver
import Test.Tasty.Silver.Advanced (readFileMaybe)
import Data.Maybe
import System.FilePath
import qualified System.Process.Text as PT
import qualified Data.Text as T
import Data.Text.Encoding
import Data.Array
import System.Exit
import System.Directory

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
  inpFiles <- getAgdaFilesInDir testDir
  agdaBin <- getAgdaBin

  let tests' = map (mkFailTest agdaBin) inpFiles

  return $ testGroup "Fail" tests'

data AgdaResult
  = AgdaResult T.Text -- the cleaned stderr? stdout?
  | AgdaUnexpectedSuccess ProgramResult


{-
diffRes :: T.Text -> T.Text -> GDiff
diffRes t1 t2 =
  if t1' == t2'
    then
      Equal
    else
      DiffText t1 t2
  where
    t1' = T.replace "\n" "" t1
    t2' = T.replace "\n" "" t2
-}

mkFailTest :: FilePath -- agda binary
    -> FilePath -- inp file
    -> TestTree
mkFailTest agdaBin inp = do
  goldenVsAction testName goldenFile doRun printAgdaResult
  where testName = dropExtension $ takeFileName inp
        goldenFile = (dropExtension inp) <.> ".err"
--        readGolden = fmap decodeUtf8 <$> readFileMaybe ref
--        updGolden  = (BL.writeFile goldenFile . fromStrict . encodeUtf8)
        flagFile = (dropExtension inp) <.> ".flags"

        doRun = (do
          flags <- fromMaybe [] . fmap (T.unpack . decodeUtf8) <$> readFileMaybe flagFile
          let agdaArgs = ["-v0", "-i" ++ testDir, "-itest/" , inp, "--ignore-interfaces"] ++ words flags
          res@(ret, stdout, _) <- PT.readProcessWithExitCode agdaBin agdaArgs T.empty

          if ret == ExitSuccess
            then
              return $ AgdaUnexpectedSuccess res
            else
              AgdaResult <$> clean stdout
          )

printAgdaResult :: AgdaResult -> T.Text
printAgdaResult (AgdaResult t) = t
printAgdaResult (AgdaUnexpectedSuccess p)= "AGDA_UNEXPECTED_SUCCESS\n\n" `T.append` printProcResult p

clean :: T.Text -> IO T.Text
clean inp = do
  pwd <- getCurrentDirectory

  return $ clean' pwd inp
  where
    mkRegex r = either (error "Invalid regex in clean") id $
      RT.compile R.defaultCompOpt R.defaultExecOpt r
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

replace :: R.Regex -> T.Text -> T.Text -> T.Text
replace rgx new inp =
  fst $ foldl repl (inp, 0) matches
  where
    matches = R.matchAll rgx inp
    repl :: (T.Text, Int) -> R.MatchArray -> (T.Text, Int)
    repl (t, globalOffset) match =
      (T.take ix t `T.append` new `T.append` T.drop (ix + len) t, globalOffset + lenDiff)
      where
        (off, len) = match ! 0
        ix = off - globalOffset
        lenDiff = len - (T.length new)
