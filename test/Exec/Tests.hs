{-# LANGUAGE CPP #-} -- GHC 7.4.2 requires this indentation. See Issue 1460.
{-# LANGUAGE DoAndIfThenElse      #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Exec.Tests where

import Test.Tasty
import Test.Tasty.Silver.Advanced (readFileMaybe)
import Test.Tasty.Silver
import qualified Data.Text as T
import Data.Text.Encoding
import System.IO.Temp
import System.FilePath
import System.Exit
import System.Process.Text as PT

#if __GLASGOW_HASKELL__ <= 708
import Control.Applicative ((<$>))
#endif

import System.Environment
import Data.Maybe
import Data.Char
import qualified Data.Set as S
import System.Directory (getDirectoryContents)

type ProgramResult = (ExitCode, T.Text, T.Text)

data ExecResult
  = CompileFailed
    { result :: ProgramResult }
  | ExecutedProg
    { result :: ProgramResult }
  deriving (Show, Read, Eq)

data Compiler = MAlonzo | UHC
  deriving (Show, Read, Eq)

enabledCompilers :: [Compiler]
enabledCompilers = [ MAlonzo{-, UHC -} ]

tests :: IO TestTree
tests = do
  ts <- mapM forComp enabledCompilers
  return $ testGroup "Exec" ts
  where forComp comp = testGroup (show comp) <$> sequence [simpleTests comp, stdlibTests comp ]


-- | Gets the program executable. If an environment variable
-- YYY_BIN is defined (with yyy converted to upper case),
-- the value of it is returned. Otherwise, the input value
-- is returned unchanged.
getProg :: String -> IO FilePath
getProg prog = fromMaybe prog <$> getProg1 (map toUpper prog ++ "_BIN")

getProg1 :: String -> IO (Maybe FilePath)
getProg1 prog = do
  env <- getEnvironment
  case lookup prog env of
      Nothing -> return Nothing
      (Just x) -> return $ Just x

agdaExts :: S.Set String
agdaExts = S.fromList [".agda", ".lagda"]

getAgdaFilesInDir :: String -> IO [FilePath]
getAgdaFilesInDir dir = map (dir </>) . filter (flip S.member agdaExts . takeExtension) <$> getDirectoryContents dir

simpleTests :: Compiler -> IO TestTree
simpleTests comp = do
  let testDir = "test" </> "Exec" </> "simple"
  inps <- getAgdaFilesInDir testDir
  testGroup "simple" <$> mapM (agdaRunProgGoldenTest testDir comp [testDir, "test/"]) inps

stdlibTests :: Compiler -> IO TestTree
stdlibTests comp = do
  let testDir = "test" </> "Exec" </> "with-stdlib"
  inps <- getAgdaFilesInDir testDir
  testGroup "with-stdlib" <$> mapM (agdaRunProgGoldenTest testDir comp [testDir, "std-lib" </> "src"]) inps

agdaRunProgGoldenTest :: FilePath     -- ^ directory where to run the tests.
    -> Compiler
    -> [FilePath] -- ^ Agda include paths.
    -> FilePath -- ^ relative path to agda input file.
    -> IO TestTree
agdaRunProgGoldenTest dir comp incDirs inp = do
  agdaBin <- getProg "agda"

  let inpFile = (dropExtension inp) <.> ".inp"
  let goldenFile = (dropExtension inp) <.> ".out"
  let testName = dropExtension $ takeFileName inp

  let doRun = withTempDirectory dir testName (\compDir -> do
      -- compile file
      let defArgs = ["--ignore-interfaces", "--compile-dir", compDir] ++ map ("-i" ++) incDirs ++ [inp]
      args <- (++ defArgs) <$> argsForComp comp
      res@(ret, _, _) <- PT.readProcessWithExitCode agdaBin args T.empty
      -- maybe we should write sout to a file instead, so that we can actually inspect it more easily
      if ret /= ExitSuccess then
        return $ CompileFailed res
      else do
        -- read input file, if it exists
        inp' <- maybe T.empty decodeUtf8 <$> readFileMaybe inpFile
        -- now run the new program
        let exec = getExecForComp comp compDir inp
        res' <- PT.readProcessWithExitCode exec [] inp'
        return $ ExecutedProg res'
      )

  return $ goldenVsAction testName goldenFile doRun printExecResult

  where argsForComp MAlonzo = return ["--compile"]
        argsForComp UHC     = do
            uhc <- getProg1 "UHC_BIN"
            let uhcBinArg = maybe [] (\x -> ["--uhc-bin", x]) uhc
            -- TODO remove the memory arg again, as soon as we fixed the memory leak
            return $ ["--uhc"] ++ uhcBinArg ++ ["+RTS", "-K50m", "-RTS"]
        -- gets the generated executable path
        getExecForComp MAlonzo compDir inpFile = compDir </> (takeFileName $ dropExtension inpFile)
        getExecForComp UHC compDir inpFile = compDir </> "UHC" </> (takeFileName $ dropExtension inpFile)

printExecResult :: ExecResult -> T.Text
printExecResult (CompileFailed r) = "COMPILE_FAILED\n\n" `T.append` printProcResult r
printExecResult (ExecutedProg r)  = "EXECUTED_PROGRAM\n\n" `T.append` printProcResult r
