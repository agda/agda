{-# LANGUAGE DoAndIfThenElse      #-}

module Main where

import qualified Compiler.Tests as COMPILER
import qualified Succeed.Tests as SUCCEED
import qualified Fail.Tests as FAIL
import qualified Interactive.Tests as INTERACTIVE
import qualified Internal.Tests as INTERNAL
import qualified LaTeXAndHTML.Tests as LATEXHTML
import qualified LibSucceed.Tests as LIBSUCCEED
import qualified UserManual.Tests as USERMANUAL
import qualified Bugs.Tests as BUGS

import Test.Tasty as T
import Test.Tasty.Silver.Interactive as TM
import Test.Tasty.Silver.Filter (RegexFilter)

import System.Exit

import Utils

main :: IO ()
main = do
  agdaBin <- doesEnvContain "AGDA_BIN"
  if agdaBin
    then
      tests >>= TM.defaultMain1 disabledTests
    else do
      putStrLn $ unlines
            [ "The AGDA_BIN environment variable is not set. Do not execute"
            , "these tests directly using \"cabal test\" or \"cabal install --run-tests\", instead"
            , "use the Makefile."
            , "Are you maybe using the Makefile together with an old cabal-install version?"
            , "Versions of cabal-install before 1.20.0.0 have a bug and will trigger this error."
            , "The Makefile requires cabal-install 1.20.0.0 or later to work properly."
            , "See also Issue #1489 and #1490."
            ]
      exitWith (ExitFailure 1)

-- | All tests covered by the tasty testsuite.
tests :: IO TestTree
tests = do
  testGroup "all" {- . concat -} <$> do
    sequence $
      -- N.B.: This list is written using (:) so that lines can be swapped easily:
      -- (The number denotes the order of the Makefile as of 2021-08-25.)
      {- 5 -} sg LATEXHTML.tests   :
      {- 3 -} sg BUGS.tests        :
      {- 1 -} sg SUCCEED.tests     :
      {- 6 -} pu INTERNAL.tests    :
      {- 9 -} sg USERMANUAL.tests  :
      {- 4 -} pu INTERACTIVE.tests :
      {- 2 -} sg FAIL.tests        :
      {- 7 -} sg COMPILER.tests    :
      {- 8 -} sg LIBSUCCEED.tests  :
      []
  where
  sg = id
  pu = pure
  -- If one @tests@ returns a list of test trees, use these wrappers:
  -- sg m = (:[]) <$> m
  -- pu x = pure [x]


disabledTests :: [RegexFilter]
disabledTests = concat
  [ COMPILER.disabledTests
  , LIBSUCCEED.disabledTests
  , LATEXHTML.disabledTests
  ]
