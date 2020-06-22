{-# LANGUAGE CPP               #-}
{-# LANGUAGE DoAndIfThenElse   #-}

module UserManual.Tests (tests, examplesInUserManual) where

import Succeed.Tests (mkSucceedTest)

import Test.Tasty
import System.FilePath

import Utils

testDir :: FilePath
testDir = "doc" </> "user-manual"

-- | These files are tested by the LaTeX test suite.

examplesInUserManual :: [FilePath]
examplesInUserManual = map ((testDir </> "tools") </>)
  [ "acmart-pdflatex.lagda.tex"
  , "article-pdflatex.lagda.tex"
  , "beamer-pdflatex.lagda.tex"
-- xelatex can only find system fonts on MacOS making these tests fail
#ifndef darwin_HOST_OS
  , "acmart-xelatex.lagda.tex"
  , "article-luaxelatex-different-fonts.lagda.tex"
  , "article-luaxelatex.lagda.tex"
  , "beamer-luaxelatex.lagda.tex"
#endif
  ]

tests :: IO TestTree
tests = do
  inpFiles <-
    -- The tex files (examplesInUserManual above) are tested by the LaTeX test suite
    filter ((/= ".tex") . takeExtension) .
    -- Files under _build should not be tested.
    filter ((/= ["_build"]) . take 1 . drop 2 . splitDirectories) <$>
      getAgdaFilesInDir Rec testDir

  -- Andreas, Victor, 2016-07-25:
  -- Don't --ignore-interfaces for user manual test!
  -- Otherwise parts of the standard library are type-checked again.
  -- Ulf, 2017-02-24: Or, we could just not depend on the standard library
  -- for the user manual...
  let extraOpts = ["--ignore-interfaces"] :: [String]

  let tests' = map (mkSucceedTest extraOpts testDir) inpFiles

  return $ testGroup "UserManual" tests'
