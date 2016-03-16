{-# LANGUAGE CPP                  #-}
{-# LANGUAGE DoAndIfThenElse      #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE PatternGuards        #-}

module Compiler.Tests where

import Utils
import Test.Tasty
import Test.Tasty.Silver.Advanced (readFileMaybe)
import Test.Tasty.Silver
import Test.Tasty.Silver.Filter
import qualified Data.Text as T
import Data.Text.Encoding
import Data.Monoid
import Data.List
import System.IO.Temp
import System.FilePath
import System.Exit
import System.Process.Text as PT

#if __GLASGOW_HASKELL__ <= 708
import Control.Applicative ((<$>))
#endif
#if __GLASGOW_HASKELL__ <= 706
import Control.Monad ( void )
#endif

import Control.Monad (forM)
import Data.Maybe

type GHCArgs = [String]

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
enabledCompilers = [ MAlonzo, UHC ]

data CompilerOptions
  = CompilerOptions
    { extraAgdaArgs :: AgdaArgs
    } deriving (Show, Read)

data TestOptions
  = TestOptions
    { forCompilers   :: [(Compiler, CompilerOptions)]
    , runtimeOptions :: [String]
    , executeProg    :: Bool
    } deriving (Show, Read)

defaultOptions :: TestOptions
defaultOptions = TestOptions
  { forCompilers   = [ (c, co) | c <- enabledCompilers ]
  , runtimeOptions = []
  , executeProg    = True
  }
  where co = CompilerOptions []

disabledTests :: [RegexFilter]
disabledTests =
  [ -- See Issue 1866
    RFInclude "Compiler/UHC/with-stdlib/.*"
-- See issue 1528
  , RFInclude "Compiler/.*/simple/Sharing"
-- Disable UHC backend tests if the backend is also disabled.
#if !defined(UHC_BACKEND)
  , RFInclude "Compiler/UHC/"
#endif
  ]

tests :: IO TestTree
tests = do
  ts <- mapM forComp enabledCompilers
  return $ testGroup "Compiler" ts
  where forComp comp = testGroup (show comp) . catMaybes
            <$> sequence
                [ Just <$> simpleTests comp
                , Just <$> stdlibTests comp
                , specialTests comp]

simpleTests :: Compiler -> IO TestTree
simpleTests comp = do
  let testDir = "test" </> "Compiler" </> "simple"
  inps <- getAgdaFilesInDir NonRec testDir

  tests' <- forM inps $ \inp -> do
    opts <- readOptions inp
    return $
      agdaRunProgGoldenTest testDir comp
        (return $ ["-i" ++ testDir, "-itest/"] ++ compArgs comp) inp opts
  return $ testGroup "simple" $ catMaybes tests'

  where compArgs :: Compiler -> AgdaArgs
        compArgs UHC = []
        compArgs MAlonzo = ghcArgsAsAgdaArgs ["-itest/"]

-- The Compiler tests using the standard library are horribly
-- slow at the moment (1min or more per test case).
stdlibTests :: Compiler -> IO TestTree
stdlibTests comp = do
  let testDir = "test" </> "Compiler" </> "with-stdlib"
  inps <- getAgdaFilesInDir NonRec testDir

  let extraArgs :: [String]
      extraArgs = [ "-i" ++ testDir, "-i" ++ "std-lib" </> "src", "-istd-lib" ]

  let rtsOptions :: [String]
      rtsOptions = [ "+RTS", "-H1G", "-M1.5G", "-RTS" ]

  tests' <- forM inps $ \inp -> do
    opts <- readOptions inp
    return $
      agdaRunProgGoldenTest testDir comp (return $ extraArgs ++ rtsOptions) inp opts
  return $ testGroup "with-stdlib" $ catMaybes tests'


specialTests :: Compiler -> IO (Maybe TestTree)
specialTests MAlonzo = do
  let t = fromJust $
            agdaRunProgGoldenTest1 testDir MAlonzo (return extraArgs)
              (testDir </> "ExportTestAgda.agda") defaultOptions cont

  return $ Just $ testGroup "special" [t]
  where extraArgs = ["-i" ++ testDir, "-itest/", "--no-main", "--ghc-dont-call-ghc"]
        testDir = "test" </> "Compiler" </> "special"
        cont compDir out err = do
            (ret, sout, _) <- PT.readProcessWithExitCode "runghc"
                    [ "-itest/"
                    ,"-i" ++ compDir
                    , testDir </> "ExportTest.hs"
                    ]
                    T.empty
            -- ignore stderr, as there may be some GHC warnings in it
            return $ ExecutedProg (ret, out <> sout, err)
specialTests UHC = return Nothing

ghcArgsAsAgdaArgs :: GHCArgs -> AgdaArgs
ghcArgsAsAgdaArgs = map f
  where f = ("--ghc-flag=" ++)

agdaRunProgGoldenTest :: FilePath     -- ^ directory where to run the tests.
    -> Compiler
    -> IO AgdaArgs     -- ^ extra Agda arguments
    -> FilePath -- ^ relative path to agda input file.
    -> TestOptions
    -> Maybe TestTree
agdaRunProgGoldenTest dir comp extraArgs inp opts =
      agdaRunProgGoldenTest1 dir comp extraArgs inp opts (\compDir out err -> do
        if executeProg opts then do
          -- read input file, if it exists
          inp' <- maybe T.empty decodeUtf8 <$> readFileMaybe inpFile
          -- now run the new program
          let exec = getExecForComp comp compDir inpFile
          (ret, out', err') <- PT.readProcessWithExitCode exec (runtimeOptions opts) inp'
          return $ ExecutedProg (ret, out <> out', err <> err')
        else
          return CompileSucceeded
        )
  where inpFile = dropExtension inp <.> ".inp"

agdaRunProgGoldenTest1 :: FilePath     -- ^ directory where to run the tests.
    -> Compiler
    -> IO AgdaArgs     -- ^ extra Agda arguments
    -> FilePath -- ^ relative path to agda input file.
    -> TestOptions
    -> (FilePath -> T.Text -> T.Text -> IO ExecResult) -- continuation if compile succeeds, gets the compilation dir
    -> Maybe TestTree
agdaRunProgGoldenTest1 dir comp extraArgs inp opts cont
  | (Just cOpts) <- lookup comp (forCompilers opts) =
      Just $ goldenVsAction testName goldenFile (doRun cOpts) printExecResult
  | otherwise = Nothing
  where goldenFile = dropExtension inp <.> ".out"
        testName   = asTestName dir inp

        doRun cOpts = withTempDirectory dir testName (\compDir -> do
          -- get extra arguments
          extraArgs' <- extraArgs
          -- compile file
          let cArgs   = cleanUpOptions (extraAgdaArgs cOpts)
              defArgs = ["--ignore-interfaces" | notElem "--no-ignore-interfaces" (extraAgdaArgs cOpts)] ++
                        ["--no-default-libraries"] ++
                        ["--compile-dir", compDir, "-v0"] ++ extraArgs' ++ cArgs ++ [inp]
          args <- (++ defArgs) <$> argsForComp comp
          res@(ret, out, err) <- readAgdaProcessWithExitCode args T.empty

          case ret of
            ExitSuccess -> cont compDir out err
            ExitFailure _ -> return $ CompileFailed res
          )

        argsForComp MAlonzo = return ["--compile"]
        argsForComp UHC     = do
            uhc <- getEnvVar "UHC_BIN"
            let uhcBinArg = maybe [] (\x -> ["--uhc-bin", x]) uhc
            -- TODO remove the memory arg again, as soon as we fixed the memory leak
            return $ ["--uhc"] ++ uhcBinArg ++ ["+RTS", "-K50m", "-RTS"]

readOptions :: FilePath -- file name of the agda file
    -> IO TestOptions
readOptions inpFile =
  maybe defaultOptions (read . T.unpack . decodeUtf8) <$> readFileMaybe optFile
  where optFile = dropExtension inpFile <.> ".options"

cleanUpOptions :: AgdaArgs -> AgdaArgs
cleanUpOptions = filter clean
  where
    clean :: String -> Bool
    clean "--no-ignore-interfaces"         = False
    clean o | isPrefixOf "--ghc-flag=-j" o = hasGHCJobsFlag
    clean _                                = True

-- gets the generated executable path
getExecForComp :: Compiler -> FilePath -> FilePath -> FilePath
getExecForComp _ compDir inpFile = compDir </> (takeFileName $ dropExtension inpFile)

printExecResult :: ExecResult -> T.Text
printExecResult (CompileFailed r) = "COMPILE_FAILED\n\n" `T.append` printProcResult r
printExecResult CompileSucceeded  = "COMPILE_SUCCEEDED"
printExecResult (ExecutedProg r)  = "EXECUTED_PROGRAM\n\n" `T.append` printProcResult r
