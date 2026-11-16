
module Compiler.Tests where

import Utils
import Test.Tasty
import Test.Tasty.HUnit (assertFailure)
import Test.Tasty.Silver
import Test.Tasty.Silver.Filter
import Data.Bits (finiteBitSize)
import qualified Data.Text as T
import Data.Text.Encoding
import Data.Monoid
import Data.List (isPrefixOf)
import System.Directory
import System.IO.Temp
import System.FilePath
import System.Environment
import System.Exit
import qualified System.Process as P
import System.Process.Text as PT


import Control.Monad (forM, when, unless)
import Data.Maybe
import Text.Read

import Agda.Utils.List
import Agda.Utils.List1 (wordsBy, toList)
import Agda.Utils.Functor ((<&>))
import Utils (readFileMaybeText)

type GHCArgs = [String]

data ExecResult
  = CompileFailed
    { result :: ProgramResult }
  | CompileSucceeded
    { result :: ProgramResult }
  | ExecutedProg
    { result :: ProgramResult }
  deriving (Show, Read, Eq)

-- | The test directory determines the expected outcome (success/failure).
data TestKind
  = Simple       -- ^ @test/Compiler/simple@.
  | Unsupported  -- ^ @test/Compiler/Unsupported@:
                 --   rejected by compiler backend because of unsupported features
                 --   (such as @--cubical@).
  | Bugs         -- ^ @test/Compiler/Bugs@: known bug in the compiler backend.
  deriving (Show, Eq)

-- | Reject the wrong outcome before comparing or updating the golden.
checkExecResult :: TestKind -> ExecResult -> IO ExecResult
checkExecResult kind actual =
  if expected then pure actual else
    assertFailure $ "Expected " ++ show kind ++ " outcome, got:\n" ++
      T.unpack (printExecResult actual)
  where
  expected = case (kind, actual) of
    (Simple, CompileSucceeded (ProgramResult ExitSuccess _ _)) -> True
    (Simple, ExecutedProg (ProgramResult ExitSuccess _ _)) -> True
    (Unsupported, CompileFailed (ProgramResult (ExitFailure 42) out _)) ->
      not $ "error: [CompilationError]" `T.isInfixOf` out
    (Bugs, ExecutedProg (ProgramResult (ExitFailure n) _ _)) -> n > 0
    _ -> False

-- | Failure golden values contain diagnostics; successful tests retain the process output.
printTestResult :: TestKind -> ExecResult -> T.Text
printTestResult Simple r = printExecResult r
printTestResult _ r = stdOut (result r) <> stdErr (result r)

data CodeOptimization = NonOptimized | Optimized | MinifiedOptimized
  deriving (Show, Read, Eq, Enum, Bounded)

data Strict = Strict | StrictData | Lazy
  deriving (Show, Read, Eq, Enum, Bounded)

data Compiler
  = MAlonzo Strict
  | JS CodeOptimization
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
allCompilers
  =  [ MAlonzo strict | strict <- [Lazy, StrictData, Strict]]
  ++ [ JS opt   | opt <- [minBound..] ]

defaultOptions :: TestOptions
defaultOptions = TestOptions
  { forCompilers   = [ (c, co) | c <- allCompilers ]
  , runtimeOptions = []
  , executeProg    = True
  }
  where co = CompilerOptions []

disabledTests :: [RegexFilter]
disabledTests =
  -----------------------------------------------------------------------------
  -- The GHC backend no longer allows compiling abstract definitions
  -- to user-chosen Haskell representations.
  disable "Compiler/MAlonzo_.*/simple/Issue2524" :
  -----------------------------------------------------------------------------
  -- The test case for #2918 stopped working when inlining of
  -- recursive pattern-matching lambdas was disabled.
  disable "Compiler/MAlonzo_.*/simple/Issue2918$" :
  -----------------------------------------------------------------------------
  -- The following test cases fail (at least at the time of writing)
  -- for the JS backend.
  disable "Compiler/JS_Optimized/simple/ModuleReexport" :
  disable "Compiler/JS_MinifiedOptimized/simple/ModuleReexport" :
  -----------------------------------------------------------------------------
  -- The following test cases are GHC backend specific and thus disabled on JS.
  disable "Compiler/JS_.*/simple/Issue2821" :
  disable "Compiler/JS_.*/simple/Issue2879-.*" :
  disable "Compiler/JS_.*/simple/Issue2909-.*" :
  disable "Compiler/JS_.*/simple/Issue2914" :
  disable "Compiler/JS_.*/simple/Issue2918$" :
  disable "Compiler/JS_.*/simple/Issue3732" :
  disable "Compiler/JS_.*/simple/VecReverseIrr" :
  disable "Compiler/JS_.*/simple/VecReverseErased" :  -- RangeError: Maximum call stack size exceeded
  -----------------------------------------------------------------------------
  []
  where disable = RFInclude

-- | Filtering out compiler tests that require Agda built with -fdebug.

fdebugTestFilter :: [RegexFilter]
fdebugTestFilter =
-- This list was crafted using
--    grep -RP '(?<!-- ){-# OPTIONS.* -v' | grep Compiler/
--  and screening the results (e.g. for comments)
  [ disable "Compiler/simple/UnusedArguments"
  , disable "Compiler/simple/EraseRefl"
  , disable "Compiler/simple/InlineRecursive"
  , disable "Compiler/simple/Word"
  , disable "Compiler/simple/CompileNumbers"
  , disable "Compiler/simple/CaseOnCase"
  , disable "Compiler/simple/CompareNat"
  , disable "Compiler/simple/CompileCatchAll"
  ]
  where disable = RFInclude

-- | Filtering out compiler tests using the Agda standard library.

stdlibTestFilter :: [RegexFilter]
stdlibTestFilter =
  [ disable "Compiler/.*/with-stdlib"
  ]
  where disable = RFInclude

tests :: IO TestTree
tests = do
  nodeBin    <- findExecutable "node"
  ghcVersion <- findGHCVersion
  let ghcVersionAtLeast9 = case ghcVersion of
        Just (n : _) | n >= 9 -> True
        _                     -> False
      enabledCompilers =
        [ MAlonzo s
        | s <- [Lazy, StrictData] ++
               [Strict | ghcVersionAtLeast9]
        ] ++
        [ JS opt
        | isJust nodeBin
        , opt   <- [minBound..]
        ]
  _ <- case nodeBin of
    Nothing -> putStrLn "No JS node binary found, skipping JS tests."
    Just n -> putStrLn $ "Using JS node binary at " ++ n

  ts <- forM enabledCompilers \ comp -> do
    testGroup (map spaceToUnderscore $ show comp) . catMaybes
        <$> sequence
            [ Just <$> compilerTests Simple comp
            , Just <$> compilerTests Unsupported comp
            , Just <$> compilerTests Bugs comp
            , Just <$> stdlibTests comp
            , specialTests comp]
  return $ testGroup "Compiler" ts
  where
    spaceToUnderscore ' ' = '_'
    spaceToUnderscore c = c

compilerTests :: TestKind -> Compiler -> IO TestTree
compilerTests kind comp = do
  let groupName = case kind of
        Simple -> "simple"
        Unsupported -> "Unsupported"
        Bugs -> "Bugs"
      testDir = "test" </> "Compiler" </> groupName
  inps <- getAgdaFilesInDir NonRec testDir

  tests' <- forM inps $ \inp -> do
    opts <- readOptions inp
    return $
      agdaRunProgGoldenTest kind testDir comp
        (return $ ["-i" ++ testDir, "-itest/Compiler", "-itest/"] ++ compArgs comp) inp opts
  return $ testGroup groupName $ catMaybes tests'

  where compArgs :: Compiler -> AgdaArgs
        compArgs MAlonzo{} =
          -- Compile the generated code without optimising it: the test
          -- suite only checks the behaviour of the compiled program, and
          -- GHC's -O pass dominates the runtime of each test.
          ghcArgsAsAgdaArgs ["-itest/", "-fno-excess-precision", "-O0"]
        compArgs JS{} = []

-- The Compiler tests using the standard library are horribly
-- slow at the moment (1min or more per test case).
stdlibTests :: Compiler -> IO TestTree
stdlibTests comp = do
  let testDir = "test" </> "Compiler" </> "with-stdlib"
  let inps    = map (testDir </>) ["AllStdLib.agda", "AllStdLibJS.agda"]
    -- put all tests in AllStdLib to avoid compiling the standard library
    -- multiple times

  let extraArgs :: [String]
      extraArgs =
        [ "-i" ++ testDir
        , "-i" ++ "std-lib" </> "src"
        , "-istd-lib"
        , "--warning=noUnsupportedIndexedMatch"
        ]

  let -- Note that -M4G can trigger the following error on 32-bit
      -- systems: "error in RTS option -M4G: size outside allowed
      -- range (4096 - 4294967295)".
      maxHeapSize =
        if finiteBitSize (undefined :: Int) == 32 then
          "-M2G"
        else
          "-M4G"

      rtsOptions :: [String]
      -- See Issue #3792.
      rtsOptions = [ "+RTS", "-H2G", maxHeapSize, "-RTS" ]

  tests' <- forM inps $ \inp -> do
    opts <- readOptions inp
    return $
      agdaRunProgGoldenTest Simple testDir comp (return $ extraArgs ++ rtsOptions) inp opts
  return $ testGroup "with-stdlib" $ catMaybes tests'


specialTests :: Compiler -> IO (Maybe TestTree)
specialTests c@MAlonzo{} = do
  let t = fromJust $
            agdaRunProgGoldenTest1 Simple testDir c (return extraArgs)
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
            return $ ExecutedProg (ProgramResult ret (out <> sout) err)
specialTests JS{} = return Nothing

ghcArgsAsAgdaArgs :: GHCArgs -> AgdaArgs
ghcArgsAsAgdaArgs = map f
  where f = ("--ghc-flag=" ++)

agdaRunProgGoldenTest :: TestKind
    -> FilePath     -- ^ directory where to run the tests.
    -> Compiler
    -> IO AgdaArgs     -- ^ extra Agda arguments
    -> FilePath -- ^ relative path to agda input file.
    -> TestOptions
    -> Maybe TestTree
agdaRunProgGoldenTest kind dir comp extraArgs inp opts =
      agdaRunProgGoldenTest1 kind dir comp extraArgs inp opts $ \compDir out err -> do
        if executeProg opts then do
          -- read input file, if it exists
          inp' <- fromMaybe T.empty <$> readFileMaybeText inpFile
          -- now run the new program
          let exec = getExecForComp comp compDir inpFile
          case comp of
            JS{} -> do
              env <- (("NODE_PATH", compDir) :) <$> getEnvironment
              nodePath <- fromJust <$> findExecutable "node"
              (ret, out', err') <- readProcessWithEnv env Nothing nodePath ["--stack-size=4096", exec] inp'
              out' <- cleanOutput out'
              err' <- cleanOutput err'
              return $ ExecutedProg $ ProgramResult ret (out <> out') (err <> err')
            _ -> do
              (ret, out', err') <- PT.readProcessWithExitCode exec (runtimeOptions opts) inp'
              return $ ExecutedProg $ ProgramResult ret (out <> out') (err <> err')
        else
          return $ CompileSucceeded (ProgramResult ExitSuccess out err)
  where inpFile = dropAgdaExtension inp <.> "inp"

agdaRunProgGoldenTest1 :: TestKind
    -> FilePath     -- ^ directory where to run the tests.
    -> Compiler
    -> IO AgdaArgs     -- ^ extra Agda arguments
    -> FilePath -- ^ relative path to agda input file.
    -> TestOptions
    -> (FilePath -> T.Text -> T.Text -> IO ExecResult) -- continuation if compile succeeds, gets the compilation dir
    -> Maybe TestTree
agdaRunProgGoldenTest1 kind dir comp extraArgs inp opts cont
  | (Just cOpts) <- lookup comp (forCompilers opts) =
      Just $ goldenVsAction' testName goldenFile (checkExecResult kind =<< doRun cOpts) (printTestResult kind)
  | otherwise = Nothing
  where goldenFile = dropAgdaExtension inp <.> if kind == Simple then "out" else "err"
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
              defArgs = ["--ignore-interfaces" | "--no-ignore-interfaces" `notElem` extraAgdaArgs cOpts] ++
                        ["--no-libraries"] ++
                        ["--compile-dir", compDir, "-v0", "-vwarning:1"] ++ extraArgs' ++ cArgs ++ [inp]
          let args = argsForComp comp ++ defArgs
          -- Unsupported programs must type-check before testing backend rejection.
          -- Otherwise --accept could record a front-end error as unsupported code.
          when (kind == Unsupported) $ do
            res@(ret, _, _) <- readAgdaProcessWithExitCode Nothing defArgs T.empty
            unless (ret == ExitSuccess) $
              assertFailure $ "Unsupported test failed to type-check:\n" ++
                T.unpack (printProgramResult $ toProgramResult res)
          res@(ret, out, err) <- readAgdaProcessWithExitCode Nothing args T.empty

          absDir <- canonicalizePath dir
          removePaths [absDir, compDir] <$> case ret of
            ExitSuccess | kind == Unsupported ->
              pure $ CompileSucceeded $ ProgramResult ExitSuccess out err
            ExitSuccess -> cont compDir out err
            ExitFailure _ -> return $ CompileFailed $ toProgramResult res
          )

        argsForComp :: Compiler -> [String]
        argsForComp (MAlonzo s) = [ "--compile" ] ++
          [ "--ghc-dont-call-ghc" | kind == Unsupported ] ++ case s of
          Lazy       -> []
          StrictData -> ["--ghc-strict-data"]
          Strict     -> ["--ghc-strict"]
        argsForComp (JS opt) = [ "--js", "--js-es6" ] ++ [ "--js-verify" | kind == Simple ]
          ++ case opt of
            NonOptimized      -> []
            Optimized         -> [ "--js-optimize" ]
            MinifiedOptimized -> [ "--js-optimize", "--js-minify" ]

        removePaths ps = \case
          CompileFailed    r -> CompileFailed    (removePaths' r)
          CompileSucceeded r -> CompileSucceeded (removePaths' r)
          ExecutedProg     r -> ExecutedProg     (removePaths' r)
          where
          removePaths' (ProgramResult c out err) = ProgramResult c (rm out) (rm err)

          rm = foldr (.) id $
               map (\p -> T.concat . T.splitOn (T.pack p)) ps

readOptions :: FilePath -- file name of the agda file
    -> IO TestOptions
readOptions inpFile = readFileMaybeText optFile <&> \case
    Nothing -> defaultOptions
    (Just optsBS) ->
      case readMaybe . T.unpack $ optsBS of
        Nothing -> error $ "Failed to parse options inside file " <> optFile
        (Just optsParsed) -> optsParsed
  where optFile = dropAgdaOrOtherExtension inpFile <.> "options"

cleanUpOptions :: AgdaArgs -> AgdaArgs
cleanUpOptions = filter clean
  where
    clean :: String -> Bool
    clean "--no-ignore-interfaces"         = False
    clean o | "--ghc-flag=-j" `isPrefixOf` o = True
    clean _                                = True

-- gets the generated executable path
getExecForComp :: Compiler -> FilePath -> FilePath -> FilePath
getExecForComp (JS opt) compDir inpFile
  = compDir </> ("jAgda." ++ takeFileName (dropAgdaOrOtherExtension inpFile) ++ ".mjs")
getExecForComp _ compDir inpFile = compDir </> takeFileName (dropAgdaOrOtherExtension inpFile)

printExecResult :: ExecResult -> T.Text
printExecResult (CompileFailed r)    = "COMPILE_FAILED\n\n"    <> printProgramResult r
printExecResult (CompileSucceeded r) = "COMPILE_SUCCEEDED\n\n" <> printProgramResult r
printExecResult (ExecutedProg r)     = "EXECUTED_PROGRAM\n\n"  <> printProgramResult r

-- | Tries to figure out the version of the program @ghc@ (if such a
-- program can be found).

findGHCVersion :: IO (Maybe [Integer])
findGHCVersion = do
  (code, version, _) <-
    P.readProcessWithExitCode "ghc" ["--numeric-version"] ""
  case code of
    ExitFailure{} -> return Nothing
    ExitSuccess   -> return $
      sequence $
      concat $
      map (map (readMaybe . toList) . wordsBy (== '.')) $
      take 1 $
      lines version
