{-# LANGUAGE CPP #-} -- GHC 7.4.2 requires this indentation. See Issue 1460.
{-# LANGUAGE DoAndIfThenElse      #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Exec.Tests where

import Test.Tasty
import Test.Tasty.Silver.Advanced (readFileMaybe)
import Test.Tasty.Silver
import Test.Tasty.Silver.Filter
import qualified Data.Text as T
import Data.Text.Encoding
import System.IO.Temp
import System.FilePath
import System.Exit
import System.Process.Text as PT
#if MIN_VERSION_process(1,2,3)
import System.Process (callProcess, proc, readCreateProcess, CreateProcess (..))
#else
import System.Process (callProcess)
#endif


#if __GLASGOW_HASKELL__ <= 708
import Control.Applicative ((<$>))
#endif

import System.Environment
import Data.Maybe
import Data.Char
import qualified Data.Set as S
import System.Directory

type ProgramResult = (ExitCode, T.Text, T.Text)
type AgdaArgs = [String]

data ExecResult
  = CompileFailed
    { result :: ProgramResult }
  | ExecutedProg
    { result :: ProgramResult }
  deriving (Show, Read, Eq)

data Compiler = MAlonzo | UHC
  deriving (Show, Read, Eq)

enabledCompilers :: [Compiler]
enabledCompilers = [ MAlonzo, UHC ]

disabledTests :: [RegexFilter]
disabledTests =
-- The Exec tests using the standard library are horribly
-- slow at the moment (1min or more per test case).
-- Disable them by default for now.
  [ RFInclude "Exec/.*/with-stdlib"
-- See issue 1414
  , RFInclude "Exec/MAlonzo/simple/FlexibleInterpreter"
-- Disabled for now, until the UHC backend is a bit more stable.
  , RFInclude "Exec/UHC/"
  ]

tests :: IO TestTree
tests = do
  ts <- mapM forComp enabledCompilers
  return $ testGroup "Exec" ts
  where forComp comp = testGroup (show comp) <$> sequence [simpleTests comp, stdlibTests comp ]


getAgdaBin :: IO FilePath
getAgdaBin = do
  agda <- getProg1 "AGDA_BIN"
  case agda of
    Just x -> return x
    Nothing -> fail "AGDA_BIN environment variable not set, aborting..."

-- | Gets the program executable. If an environment variable
-- YYY_BIN is defined (with yyy converted to upper case),
-- the value of it is returned. Otherwise, the input value
-- is returned unchanged.
getProg :: String -> IO FilePath
getProg prog = fromMaybe prog <$> getProg1 (map toUpper prog ++ "_BIN")

getProg1 :: String -> IO (Maybe FilePath)
getProg1 prog = do
  env' <- getEnvironment
  case lookup prog env' of
      Nothing -> return Nothing
      (Just x) -> return $ Just x

agdaExts :: S.Set String
agdaExts = S.fromList [".agda", ".lagda"]

getAgdaFilesInDir :: String -> IO [FilePath]
getAgdaFilesInDir dir = map (dir </>) . filter (flip S.member agdaExts . takeExtension) <$> getDirectoryContents dir

simpleTests :: Compiler -> IO TestTree
simpleTests comp = do
  agdaBin <- getAgdaBin
  let testDir = "test" </> "Exec" </> "simple"
  inps <- getAgdaFilesInDir testDir

  let mkTest = (\args inp ->
        agdaRunProgGoldenTest agdaBin testDir comp ((["-i" ++ testDir, "-itest/"] ++) <$> args) inp
        )
  setup comp (\args -> testGroup "simple"
        $ map (mkTest args) inps)
  where setup :: Compiler -> (IO AgdaArgs -> TestTree) -> IO TestTree
        setup UHC tree = return $ tree (return [])
        setup MAlonzo tree = withGhcLibs ["test/"] tree

stdlibTests :: Compiler -> IO TestTree
stdlibTests comp = do
  agdaBin <- getAgdaBin
  let testDir = "test" </> "Exec" </> "with-stdlib"
  inps <- getAgdaFilesInDir testDir

  let mkTest = (\args inp ->
        agdaRunProgGoldenTest agdaBin testDir comp ((["-i" ++ testDir, "-i" ++ "std-lib" </> "src"] ++) <$> args) inp
        )
  setup comp (\args -> testGroup "with-stdlib"
        $ map (mkTest args) inps)
  where setup :: Compiler -> (IO AgdaArgs -> TestTree) -> IO TestTree
        setup UHC tree = return $ tree (return [])
        setup MAlonzo tree = withGhcLibs ["std-lib/ffi/"] tree



-- Sets up a temporary package db and installs the given packages there.
withGhcLibs :: [String] -- ^ path to the package directories to install.
    -> (IO AgdaArgs -> TestTree)
    -> IO TestTree
withGhcLibs pkgDirs mkTree = do
  let createPkgDb = (do
        pwd <- getCurrentDirectory
        tempDir <- createTempDirectory pwd "exec-test-pkgs"
        let pkgDb = tempDir </> "pkgdb"
        callProcess "ghc-pkg" ["init", pkgDb]
        mapM_ (installPkg tempDir pkgDb) pkgDirs
        return (tempDir, pkgDb)
        )
  let rmPkgDb = removeDirectoryRecursive . fst

  return $ withResource createPkgDb rmPkgDb (\si -> mkTree (mkArgs <$> si))
  where installPkg :: FilePath -> FilePath -> FilePath -> IO ()
        installPkg tempDir pkgDb pkgDir = do
            callProcess1 pkgDir "runhaskell" ["Setup.hs", "configure", "--prefix=" ++ tempDir, "--package-db=" ++ pkgDb]
            callProcess1 pkgDir "runhaskell" ["Setup.hs", "build"]
            callProcess1 pkgDir "runhaskell" ["Setup.hs", "install"]
        mkArgs :: (FilePath, FilePath) -> AgdaArgs
        mkArgs (_, pkgDb) = ["--ghc-flag=-package-db=" ++ pkgDb]
        callProcess1 :: FilePath -> FilePath -> [String] -> IO ()
#if MIN_VERSION_process(1,2,3)
        callProcess1 wd cmd args = readCreateProcess ((proc cmd args) {cwd = Just wd}) "" >> return ()
#else
        -- trying to use process 1.2.3.0 with GHC 7.4 leads to cabal hell,
        -- so we really want to support older versions of process for the time being.
        callProcess1 wd cmd args = do
            oldPwd <- getCurrentDirectory
            setCurrentDirectory wd
            callProcess cmd args
            setCurrentDirectory oldPwd
#endif

agdaRunProgGoldenTest :: FilePath -- ^ path to the agda executable.
    -> FilePath     -- ^ directory where to run the tests.
    -> Compiler
    -> IO AgdaArgs     -- ^ extra Agda arguments
    -> FilePath -- ^ relative path to agda input file.
    -> TestTree
agdaRunProgGoldenTest agdaBin dir comp extraArgs inp =
  goldenVsAction testName goldenFile doRun printExecResult
  where inpFile = (dropExtension inp) <.> ".inp"
        goldenFile = (dropExtension inp) <.> ".out"
        testName = dropExtension $ takeFileName inp

        doRun = withTempDirectory dir testName (\compDir -> do
          -- get extra arguments
          extraArgs' <- extraArgs
          -- compile file
          let defArgs = ["--ignore-interfaces", "--compile-dir", compDir] ++ extraArgs' ++ [inp]
          args <- (++ defArgs) <$> argsForComp comp
          res@(ret, _, _) <- PT.readProcessWithExitCode agdaBin args T.empty
          -- maybe we should write sout to a file instead, so that we can actually inspect it more easily
          if ret /= ExitSuccess then
            return $ CompileFailed res
          else do
            -- read input file, if it exists
            inp' <- maybe T.empty decodeUtf8 <$> readFileMaybe inpFile
            -- now run the new program
            let exec = getExecForComp comp compDir
            res' <- PT.readProcessWithExitCode exec [] inp'
            return $ ExecutedProg res'
          )

        argsForComp MAlonzo = return ["--compile"]
        argsForComp UHC     = do
            uhc <- getProg1 "UHC_BIN"
            let uhcBinArg = maybe [] (\x -> ["--uhc-bin", x]) uhc
            -- TODO remove the memory arg again, as soon as we fixed the memory leak
            return $ ["--uhc"] ++ uhcBinArg ++ ["+RTS", "-K50m", "-RTS"]
        -- gets the generated executable path
        getExecForComp MAlonzo compDir  = compDir </> (takeFileName $ dropExtension inpFile)
        getExecForComp UHC compDir = compDir </> "UHC" </> (takeFileName $ dropExtension inpFile)

printExecResult :: ExecResult -> T.Text
printExecResult (CompileFailed r) = "COMPILE_FAILED\n\n" `T.append` printProcResult r
printExecResult (ExecutedProg r)  = "EXECUTED_PROGRAM\n\n" `T.append` printProcResult r
