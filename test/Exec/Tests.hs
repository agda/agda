-- GHC 7.4.2 requires this layout for the pragmas. See Issue 1460.
{-# LANGUAGE CPP,
             DoAndIfThenElse,
             FlexibleInstances,
             OverloadedStrings,
             TypeSynonymInstances,
             PatternGuards #-}

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
import System.Process (callProcess, proc, createProcess, waitForProcess, CreateProcess (..))
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
  | CompileSucceeded
  | ExecutedProg
    { result :: ProgramResult }
  deriving (Show, Read, Eq)

data Compiler = MAlonzo | UHC
  deriving (Show, Read, Eq)

enabledCompilers :: [Compiler]
enabledCompilers = [ MAlonzo{-, UHC -} ]

data CompilerOptions
  = CompilerOptions
    { extraAgdaArgs :: AgdaArgs
    } deriving (Show, Read)

data TestOptions
  = TestOptions
    { forCompilers :: [(Compiler, CompilerOptions)]
    , executeProg :: Bool
    } deriving (Show, Read)

defaultOptions :: TestOptions
defaultOptions = TestOptions
  { forCompilers = [ (c, co) | c <- enabledCompilers ]
  , executeProg = True
  }
  where co = CompilerOptions []
  

disabledTests :: [RegexFilter]
disabledTests =
-- The Exec tests using the standard library are horribly
-- slow at the moment (1min or more per test case).
-- Disable them by default for now.
  [ RFInclude "Exec/.*/with-stdlib"
-- See issue 1414
  , RFInclude "Exec/MAlonzo/simple/FlexibleInterpreter"
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

  withSetup setup agdaBin inps testDir ["-i" ++ testDir, "-itest/"] comp "simple"
  where setup :: Compiler -> (IO (IO AgdaArgs -> TestTree)) -> IO TestTree
        setup UHC tree = tree >>= \t -> return $ t $ return []
        setup MAlonzo tree = withGhcLibs ["test/"] <$> tree

stdlibTests :: Compiler -> IO TestTree
stdlibTests comp = do
  agdaBin <- getAgdaBin
  let testDir = "test" </> "Exec" </> "with-stdlib"
  inps <- getAgdaFilesInDir testDir

  withSetup setup agdaBin inps testDir ["-i" ++ testDir, "-i" ++ "std-lib" </> "src"] comp "with-stdlib"
  where setup :: Compiler -> (IO (IO AgdaArgs -> TestTree)) -> IO TestTree
        setup UHC tree = tree >>= \t -> return $ t $ return []
        setup MAlonzo tree = withGhcLibs ["std-lib/ffi/"] <$> tree


withSetup :: (Compiler -> (IO (IO AgdaArgs -> TestTree)) -> IO TestTree) -- setup function
    -> FilePath -- Agda executable
    -> [FilePath] -- inputs
    -> FilePath -- test directory
    -> AgdaArgs -- extra agda arguments
    -> Compiler
    -> TestName -- test group name
    -> IO TestTree
withSetup setup agdaBin inps testDir extraArgs comp  testGrpNm = do
  setup comp (do
    mkTests' <- mapM mkTest inps
    return (\args ->
        testGroup testGrpNm $ catMaybes $ map ($ args) mkTests'
      )
    )
  where mkTest :: FilePath -> IO (IO AgdaArgs -> Maybe TestTree)
        mkTest = (\inp -> do
          opts <- readOptions inp
          return (\args ->
            agdaRunProgGoldenTest agdaBin testDir comp ((extraArgs  ++) <$> args) inp opts
            )
          )
    


-- Sets up a temporary package db and installs the given packages there.
withGhcLibs :: [String] -- ^ path to the package directories to install.
    -> (IO AgdaArgs -> TestTree)
    -> TestTree
withGhcLibs pkgDirs mkTree =
  withResource createPkgDb rmPkgDb (\si -> mkTree (mkArgs <$> si))
  where rmPkgDb = removeDirectoryRecursive . fst
        createPkgDb = (do
          pwd <- getCurrentDirectory
          tempDir <- createTempDirectory pwd "exec-test-pkgs"
          let pkgDb = tempDir </> "pkgdb"
          callProcess "ghc-pkg" ["init", pkgDb]
          mapM_ (installPkg tempDir pkgDb) pkgDirs
          return (tempDir, pkgDb)
          )
        installPkg :: FilePath -> FilePath -> FilePath -> IO ()
        installPkg tempDir pkgDb pkgDir = do
            callProcess1 pkgDir "runhaskell" ["Setup.hs", "configure", "--prefix=" ++ tempDir, "--package-db=" ++ pkgDb]
            callProcess1 pkgDir "runhaskell" ["Setup.hs", "build"]
            callProcess1 pkgDir "runhaskell" ["Setup.hs", "install"]
        mkArgs :: (FilePath, FilePath) -> AgdaArgs
#if __GLASGOW_HASKELL__ > 704
        mkArgs (_, pkgDb) = ["--ghc-flag=-no-user-package-db",   "--ghc-flag=-package-db=" ++ pkgDb]
#else
        mkArgs (_, pkgDb) = ["--ghc-flag=-no-user-package-conf", "--ghc-flag=-package-conf=" ++ pkgDb]
#endif
        callProcess1 :: FilePath -> FilePath -> [String] -> IO ()
#if MIN_VERSION_process(1,2,3)
        callProcess1 wd cmd args = readCreateProcess ((proc cmd args) {cwd = Just wd}) "" >> return ()
#else
        -- trying to use process 1.2.3.0 with GHC 7.4 leads to cabal hell,
        -- so we really want to support older versions of process for the time being.
        callProcess1 wd cmd args = do
            -- note: the new process will inherit stdout/stdin/stderr from us,
            -- and will spam the console a bit. This will make the UI a bit
            -- ugly, but shouldn't cause any problems.
            (_, _, _, pHandle) <- createProcess (proc cmd args) {cwd = Just wd}
            ExitSuccess <- waitForProcess pHandle
            return ()
#endif

agdaRunProgGoldenTest :: FilePath -- ^ path to the agda executable.
    -> FilePath     -- ^ directory where to run the tests.
    -> Compiler
    -> IO AgdaArgs     -- ^ extra Agda arguments
    -> FilePath -- ^ relative path to agda input file.
    -> TestOptions
    -> Maybe TestTree
agdaRunProgGoldenTest agdaBin dir comp extraArgs inp opts
  | (Just cOpts) <- lookup comp (forCompilers opts) =
      Just $ goldenVsAction testName goldenFile (doRun cOpts) printExecResult
  | otherwise = Nothing
  where inpFile = (dropExtension inp) <.> ".inp"
        goldenFile = (dropExtension inp) <.> ".out"
        testName = dropExtension $ takeFileName inp

        doRun cOpts = withTempDirectory dir testName (\compDir -> do
          -- get extra arguments
          extraArgs' <- extraArgs
          -- compile file
          let defArgs = ["--ignore-interfaces", "--compile-dir", compDir] ++ extraArgs' ++ (extraAgdaArgs cOpts) ++ [inp]
          args <- (++ defArgs) <$> argsForComp comp
          res@(ret, _, _) <- PT.readProcessWithExitCode agdaBin args T.empty
          -- maybe we should write sout to a file instead, so that we can actually inspect it more easily
          case ret of
            ExitSuccess | executeProg opts -> do
              -- read input file, if it exists
              inp' <- maybe T.empty decodeUtf8 <$> readFileMaybe inpFile
              -- now run the new program
              let exec = getExecForComp comp compDir
              res' <- PT.readProcessWithExitCode exec [] inp'
              return $ ExecutedProg res'
            ExitSuccess | otherwise -> return $ CompileSucceeded
            ExitFailure _ -> return $ CompileFailed res
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

readOptions :: FilePath -- file name of the agda file
    -> IO TestOptions
readOptions inpFile =
  maybe defaultOptions (read . T.unpack . decodeUtf8) <$> readFileMaybe optFile
  where optFile = dropExtension inpFile <.> ".options"

printExecResult :: ExecResult -> T.Text
printExecResult (CompileFailed r) = "COMPILE_FAILED\n\n" `T.append` printProcResult r
printExecResult (CompileSucceeded) = "COMPILE_SUCCEEDED"
printExecResult (ExecutedProg r)  = "EXECUTED_PROGRAM\n\n" `T.append` printProcResult r
