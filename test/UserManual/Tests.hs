{-# LANGUAGE CPP               #-}
{-# LANGUAGE DoAndIfThenElse   #-}
{-# LANGUAGE OverloadedStrings #-}

module UserManual.Tests where

import Succeed.Tests (mkSucceedTest)

import Test.Tasty
import System.FilePath

import Utils

testDir :: FilePath
testDir = "doc" </> "user-manual"

tests :: IO TestTree
tests = do
  inpFiles <- getAgdaFilesInDir Rec testDir

  let tests' = map (mkSucceedTest testDir) inpFiles

  return $ testGroup "UserManual" tests'
