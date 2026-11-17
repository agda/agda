-- | Regression tests for outcome checks in the golden test runners (#8909).
module Internal.TestSuite (tests) where

import Control.Exception (try)
import Control.Monad (forM_, when)
import Data.List (isInfixOf)
import qualified Data.Text as T
import System.Directory (createDirectory, doesFileExist, removeFile)
import System.Environment (getEnvironment)
import System.Exit (ExitCode(..))
import System.FilePath ((</>), (<.>))
import System.IO.Temp (withSystemTempDirectory)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit
import Test.Tasty.Options (setOption)
import Test.Tasty.Providers (Result, run)
import Test.Tasty.Runners (TestTree(..), resultSuccessful)
import Test.Tasty.Silver.Internal (AcceptTests(..))

import qualified BuildFail.Tests as BuildFail
import qualified BuildSucceed.Tests as BuildSucceed
import qualified Compiler.Tests as Compiler
import qualified Fail.Tests as Fail
import qualified Interaction.Simple.Tests as Interaction
import qualified LaTeXAndHTML.Tests as LaTeX
import qualified Succeed.Tests as Succeed
import Utils

-- Run the golden provider itself so --accept and exceptions behave exactly as
-- they do in the outer runner, without a second process or interactive prompts.
runGolden :: Bool -> TestTree -> IO Result
runGolden accept (SingleTest _ t) =
  run (setOption (AcceptTests accept) mempty) t (const $ pure ())
runGolden _ _ = assertFailure "Expected a single golden test"

-- Check existing, missing, and already accepted failure goldens. A rejected
-- outcome must not create or overwrite any golden, even under --accept.
assertRejected :: FilePath -> T.Text -> String -> TestTree -> Assertion
assertRejected golden old diagnostic tree =
  forM_ [Nothing, Just "old output", Just old] $ \contents -> do
    exists <- doesFileExist golden
    if exists then removeFile golden else pure ()
    forM_ contents $ writeTextFile golden
    forM_ [False, True] $ \accept -> do
      result <- try (runGolden accept tree) :: IO (Either HUnitFailure Result)
      case result of
        Left e -> assertBool (show e) $ diagnostic `isInfixOf` show e
        Right r -> assertBool "Unexpected outcome passed" $ not $ resultSuccessful r
      actual <- readTextFileMaybe golden
      assertEqual "Rejected outcome changed the golden" contents actual

withFixture :: T.Text -> (FilePath -> FilePath -> IO a) -> IO a
withFixture source action = withSystemTempDirectory "issue8909" $ \dir -> do
  let inp = dir </> "Fixture.agda"
  writeTextFile inp source
  action dir inp

compilerTree :: Compiler.TestKind -> FilePath -> FilePath -> IO TestTree
compilerTree kind dir inp =
  case Compiler.agdaRunProgGoldenTest kind dir (Compiler.JS Compiler.NonOptimized)
      (pure ["-i" ++ dir]) inp Compiler.defaultOptions of
    Nothing -> assertFailure "Compiler test was disabled"
    Just t -> pure t

runtimeBug :: T.Text
runtimeBug = T.unlines
  [ "module Fixture where"
  , "open import Agda.Builtin.IO"
  , "open import Agda.Builtin.Unit"
  , "open import RuntimeBug"
  , "main : IO ⊤"
  , "main = boom"
  ]

tests :: TestTree
tests = testGroup "TestSuite" $
  [ testCase "Unexpected outcome marker spellings" $ do
      assertEqual "Failure marker" "AGDA_UNEXPECTED_FAIL" agdaUnexpectedFail
      assertEqual "Success marker" "AGDA_UNEXPECTED_SUCCESS" agdaUnexpectedSuccess
  , testCase "Expected outcomes preserve output formatting" $ do
      let success = ProgramResult ExitSuccess "warnings and output" "stderr"
          failure = ProgramResult (ExitFailure 42) "type error" "stderr"
          other = ProgramResult (ExitFailure 120) "internal error" "stderr"
      assertEqual "Success stdout" (stdOut success) =<<
        expectAgdaSuccess (success, AgdaSuccess $ Just "warning")
      assertEqual "Type error stdout" (stdOut failure) =<<
        expectAgdaFailure (failure, AgdaFailure 42 $ Just TCMError)
      assertEqual "Other failure details" (printProgramResult other) =<<
        expectAgdaFailure (other, AgdaFailure 120 $ Just ImpossibleError)
  , testCase "Unexpected outcomes use shared diagnostics" $ do
      let failure = ProgramResult (ExitFailure 42) "type error" "stderr"
          success = ProgramResult ExitSuccess "output" "stderr"
      forM_
        [ (printUnexpectedAgdaFail failure, expectAgdaSuccess (failure, AgdaFailure 42 $ Just TCMError))
        , (printUnexpectedAgdaSuccess success, expectAgdaFailure (success, AgdaSuccess Nothing))
        ] $ \(diagnostic, action) -> do
          result <- try action :: IO (Either HUnitFailure T.Text)
          case result of
            Left (HUnitFailure _ message) -> assertEqual "Unexpected diagnostic" (T.unpack diagnostic) message
            Right _ -> assertFailure "Unexpected outcome was accepted"
  , testCase "Succeed rejects errors" $
      withFixture "module Fixture where\nx : Set\nx = Set\n" $ \dir inp ->
        assertRejected (dir </> "Fixture.warn")
          agdaUnexpectedFail (T.unpack agdaUnexpectedFail)
          (Succeed.mkSucceedTest [] dir inp)
  , testCase "Fail rejects success" $
      withFixture "module Fixture where\n" $ \dir inp ->
        assertRejected (dir </> "Fixture.err")
          agdaUnexpectedSuccess (T.unpack agdaUnexpectedSuccess)
          (Fail.mkFailTest dir inp)
  , testCase "HTML rejects Agda errors" $
      withFixture "module Fixture where\nx : Set\nx = Set\n" $ \dir inp -> do
        agda <- getAgdaBin <$> getEnvironment
        assertRejected (dir </> "Fixture.html")
          "AGDA_COMPILE_FAILED" "AGDA_COMPILE_FAILED"
          (LaTeX.mkLaTeXOrHTMLTest LaTeX.HTML False agda dir inp)
  , testCase "Interaction rejects a failed process" $
      withFixture "module Fixture where\n" $ \dir inp -> do
        writeTextFile (dir </> "Fixture.in") ""
        writeTextFile (dir </> "Fixture.flags") "--this-option-does-not-exist"
        assertRejected (dir </> "Fixture.out") "" "ExitSuccess"
          (Interaction.mkSimpleTest inp)
  , testCase "LaTeX compiler errors cannot be accepted" $
      withSystemTempDirectory "issue8909-latex" $ \dir -> do
        let actual = LaTeX.LaTeXFailed ["pdflatex"]
            golden = dir </> "Fixture.tex"
            tree = goldenVsAction' "latex" golden
              (LaTeX.checkLaTeXResult False actual) (LaTeX.printLaTeXResult "")
        assertRejected golden (LaTeX.printLaTeXResult "" actual) "LATEX_COMPILE_FAILED" tree
  , testCase "Compiler directory determines expected outcome" $
      withFixture "{-# OPTIONS --cubical #-}\nmodule Fixture where\n" $ \dir inp -> do
        simple <- compilerTree Compiler.Simple dir inp
        assertRejected (dir </> "Fixture.out") "COMPILE_FAILED"
          "Expected Simple outcome" simple
        unsupported <- compilerTree Compiler.Unsupported dir inp
        r <- runGolden True unsupported
        assertBool "Backend rejection was not accepted" $ resultSuccessful r
        actual <- readTextFile (dir </> "Fixture.err")
        assertBool "Golden should contain the Agda diagnostic" $
          "error: [CubicalCompilationNotSupported]" `T.isInfixOf` actual
        bugs <- compilerTree Compiler.Bugs dir inp
        assertRejected (dir </> "Fixture.err") actual "Expected Bugs outcome" bugs
  , testCase "Unsupported rejects front-end errors" $
      withFixture "module Fixture where\nx : Set\nx = Set\n" $ \dir inp -> do
        tree <- compilerTree Compiler.Unsupported dir inp
        assertRejected (dir </> "Fixture.err") "error" "failed to type-check" tree
  , testCase "Unsupported rejects successful compilation" $
      withFixture "module Fixture where\n" $ \dir inp -> do
        tree <- compilerTree Compiler.Unsupported dir inp
        assertRejected (dir </> "Fixture.err") "" "Expected Unsupported outcome" tree
  , testCase "Bugs records runtime exceptions" $ do
      node <- doesCommandExist "node"
      when node $ withFixture runtimeBug $ \dir inp -> do
        -- This dependency throws during module initialization. --js-verify
        -- would execute it too early and turn this into a compilation failure.
        writeTextFile (dir </> "RuntimeBug.agda") $ T.unlines
          [ "module RuntimeBug where"
          , "open import Agda.Builtin.IO"
          , "open import Agda.Builtin.Unit"
          , "postulate boom : IO ⊤"
          , "{-# COMPILE JS boom = (function() { throw new Error(\"fixture bug\"); })() #-}"
          ]
        tree <- compilerTree Compiler.Bugs dir inp
        r <- runGolden True tree
        assertBool "Runtime exception was not accepted" $ resultSuccessful r
        actual <- readTextFile (dir </> "Fixture.err")
        assertBool "Golden should contain the runtime diagnostic" $
          "Error: fixture bug" `T.isInfixOf` actual
  , testCase "Successful output can still be accepted" $
      withFixture "module Fixture where\n" $ \dir inp -> do
        let golden = dir </> "Fixture.warn"
        writeTextFile golden "old output"
        r <- runGolden True $ Succeed.mkSucceedTest [] dir inp
        assertBool "Could not accept successful output" $ resultSuccessful r
        actual <- readTextFile golden
        assertEqual "Golden not updated" "" actual
  ] ++
  [ testCase ("Build outcome, expected success: " ++ show success) $
      withSystemTempDirectory "issue8909-build" $ \dir -> do
        let lib = dir </> "library"
        createDirectory lib
        writeFile (lib </> "test.agda-lib") "name: test\ninclude: .\n"
        writeFile (lib </> "Fixture.agda") $
          if success then "module Fixture where\nx : Set\nx = Set\n"
          else "module Fixture where\n"
        let (ext, diagnostic, tree) = if success then
              ("warn", agdaUnexpectedFail, BuildSucceed.mkBuildSucceedTest False lib)
              else ("err", agdaUnexpectedSuccess, BuildFail.mkBuildFailTest lib)
        assertRejected (lib <.> ext) diagnostic (T.unpack diagnostic) tree
  | success <- [False, True]
  ] ++
  [ testCase ("Compiler outcome: " ++ show expected ++ ", " ++ show actual) $
      withSystemTempDirectory "issue8909-compiler" $ \dir -> do
        let golden = dir </> if expected == Compiler.Simple then "Fixture.out" else "Fixture.err"
            tree = goldenVsAction' "compiler" golden
              (Compiler.checkExecResult expected actual) (Compiler.printTestResult expected)
        if allowed then do
          r <- runGolden True tree
          assertBool "Expected compiler outcome rejected" $ resultSuccessful r
          assertBool "No golden created" =<< doesFileExist golden
        else assertRejected golden (Compiler.printTestResult expected actual) "Expected " tree
  | let failure = ProgramResult (ExitFailure 42) "error: [CubicalCompilationNotSupported]" ""
        success = ProgramResult ExitSuccess "output" ""
  , (expected, actual, allowed) <-
      [ (Compiler.Simple, Compiler.CompileFailed failure, False)
      , (Compiler.Simple, Compiler.ExecutedProg failure, False)
      , (Compiler.Simple, Compiler.ExecutedProg success, True)
      , (Compiler.Simple, Compiler.CompileSucceeded success, True)
      , (Compiler.Unsupported, Compiler.CompileFailed failure, True)
      , (Compiler.Bugs, Compiler.ExecutedProg failure, True)
      , (Compiler.Unsupported, Compiler.ExecutedProg failure, False)
      , (Compiler.Bugs, Compiler.CompileSucceeded success, False)
      , (Compiler.Bugs, Compiler.ExecutedProg success, False)
      , (Compiler.Unsupported, Compiler.CompileSucceeded success, False)
      , (Compiler.Unsupported, Compiler.CompileFailed (ProgramResult (ExitFailure 120) "internal error" ""), False)
      , (Compiler.Unsupported, Compiler.CompileFailed (ProgramResult (ExitFailure 42) "error: [CompilationError]" ""), False)
      ]
  ]
