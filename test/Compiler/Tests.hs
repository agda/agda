{-# LANGUAGE DoAndIfThenElse      #-}
{-# LANGUAGE CPP                  #-}
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
import System.Directory
import System.IO.Temp
import System.FilePath
import System.Environment
import System.Exit
import System.Process.Text as PT

import Control.Monad (forM)
import Data.Maybe

type GHCArgs = [String]

data ExecResult
  = CompileFailed
    { result :: ProgramResult }
  | CompileSucceeded
    { result :: ProgramResult }
  | ExecutedProg
    { result :: ProgramResult }
  deriving (Show, Read, Eq)

data Compiler = MAlonzo | JS
  deriving (Show, Read, Eq)

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

allCompilers :: [Compiler]
allCompilers = [MAlonzo, JS]

defaultOptions :: TestOptions
defaultOptions = TestOptions
  { forCompilers   = [ (c, co) | c <- allCompilers ]
  , runtimeOptions = []
  , executeProg    = True
  }
  where co = CompilerOptions []

disabledTests :: [RegexFilter]
disabledTests =
  [ -- See issue 1528
    RFInclude "Compiler/.*/simple/Sharing"
  , RFInclude "Compiler/JS/simple/VecReverseIrr"
  , RFInclude "Compiler/JS/simple/Issue2821"    -- GHC backend specific
  , RFInclude "Compiler/JS/simple/Issue2914"    -- GHC backend specific
  , RFInclude "Compiler/JS/simple/Issue3732"    -- GHC backend specific
    -- Fix to 2524 is too unsafe
  , RFInclude "Compiler/.*/simple/Issue2524"
    -- Segfaulting 2640 behaves differently on travis
  , RFInclude "Compiler/.*/simple/Erasure-Issue2640"
    -- Andreas, 2018-10-23, dunno why, but VecReverseErased is broken on travis
  , RFInclude "Compiler/.*/simple/VecReverseErased"
    -- The following test cases are GHC backend specific.
  , RFInclude "Compiler/JS/simple/Issue2879-.*"
  , RFInclude "Compiler/JS/simple/Issue2909-.*"
  , RFInclude "Compiler/JS/simple/Issue2918"
  ]

tests :: IO TestTree
tests = do
  hasNode <- doesCommandExist "node"
  let enabledCompilers = [MAlonzo] ++ [JS | hasNode]

  ts <- mapM forComp enabledCompilers
  return $ testGroup "Compiler" ts
  where
    forComp comp = testGroup (show comp) . catMaybes
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
        compArgs MAlonzo = ghcArgsAsAgdaArgs ["-itest/"]
        compArgs JS = []

-- The Compiler tests using the standard library are horribly
-- slow at the moment (1min or more per test case).
stdlibTests :: Compiler -> IO TestTree
stdlibTests comp = do
  let testDir = "test" </> "Compiler" </> "with-stdlib"
  inps <- return [testDir </> "AllStdLib.agda"]
    -- put all tests in AllStdLib to avoid compiling the standard library
    -- multiple times

  let extraArgs :: [String]
      extraArgs = [ "-i" ++ testDir, "-i" ++ "std-lib" </> "src", "-istd-lib" ]

  let rtsOptions :: [String]
-- See Issue #3792.
#if __GLASGOW_HASKELL__ < 802
      rtsOptions = [ "+RTS", "-H2G", "-M3G", "-RTS" ]
#else
      rtsOptions = [ "+RTS", "-H2G", "-M2.5G", "-RTS" ]
#endif

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
specialTests JS = return Nothing

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
          case comp of
            JS -> do
              setEnv "NODE_PATH" compDir
              (ret, out', err') <- PT.readProcessWithExitCode "node" [exec] inp'
              return $ ExecutedProg (ret, out <> out', err <> err')
            _ -> do
              (ret, out', err') <- PT.readProcessWithExitCode exec (runtimeOptions opts) inp'
              return $ ExecutedProg (ret, out <> out', err <> err')
        else
          return $ CompileSucceeded (ExitSuccess, out, err)
        )
  where inpFile = dropAgdaExtension inp <.> ".inp"

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
  where goldenFile = dropAgdaExtension inp <.> ".out"
        testName   = asTestName dir inp

        -- Andreas, 2017-04-14, issue #2317
        -- Create temporary files in system temp directory.
        -- This has the advantage that upon Ctrl-C no junk is left behind
        -- in the Agda directory.
        -- doRun cOpts = withTempDirectory dir testName (\compDir -> do
        doRun cOpts = withSystemTempDirectory testName (\compDir -> do
          -- get extra arguments
          extraArgs' <- extraArgs
          -- compile file
          let cArgs   = cleanUpOptions (extraAgdaArgs cOpts)
              defArgs = ["--ignore-interfaces" | notElem "--no-ignore-interfaces" (extraAgdaArgs cOpts)] ++
                        ["--no-libraries"] ++
                        ["--compile-dir", compDir, "-v0", "-vwarning:1"] ++ extraArgs' ++ cArgs ++ [inp]
          args <- (++ defArgs) <$> argsForComp comp
          res@(ret, out, err) <- readAgdaProcessWithExitCode args T.empty

          absDir <- canonicalizePath dir
          removePaths [absDir, compDir] <$> case ret of
            ExitSuccess -> cont compDir out err
            ExitFailure _ -> return $ CompileFailed res
          )

        argsForComp :: Compiler -> IO [String]
        argsForComp MAlonzo = return ["--compile"]
        argsForComp JS = return ["--js"]

        removePaths ps r = case r of
          CompileFailed    r -> CompileFailed    (removePaths' r)
          CompileSucceeded r -> CompileSucceeded (removePaths' r)
          ExecutedProg     r -> ExecutedProg     (removePaths' r)
          where
          removePaths' (c, out, err) = (c, rm out, rm err)

          rm = foldr (.) id $
               map (\p -> T.concat . T.splitOn (T.pack p)) ps

readOptions :: FilePath -- file name of the agda file
    -> IO TestOptions
readOptions inpFile =
  maybe defaultOptions (read . T.unpack . decodeUtf8) <$> readFileMaybe optFile
  where optFile = dropAgdaOrOtherExtension inpFile <.> ".options"

cleanUpOptions :: AgdaArgs -> AgdaArgs
cleanUpOptions = filter clean
  where
    clean :: String -> Bool
    clean "--no-ignore-interfaces"         = False
    clean o | isPrefixOf "--ghc-flag=-j" o = True
    clean _                                = True

-- gets the generated executable path
getExecForComp :: Compiler -> FilePath -> FilePath -> FilePath
getExecForComp JS compDir inpFile = compDir </> ("jAgda." ++ (takeFileName $ dropAgdaOrOtherExtension inpFile) ++ ".js")
getExecForComp _ compDir inpFile = compDir </> (takeFileName $ dropAgdaOrOtherExtension inpFile)

printExecResult :: ExecResult -> T.Text
printExecResult (CompileFailed r) = "COMPILE_FAILED\n\n" `T.append` printProcResult r
printExecResult (CompileSucceeded r) = "COMPILE_SUCCEEDED\n\n" `T.append` printProcResult r
printExecResult (ExecutedProg r)  = "EXECUTED_PROGRAM\n\n" `T.append` printProcResult r
