module Utils where

import           Data.ByteString.Lazy.Char8
import           Malfunction.AST
import           Malfunction.Run
import           System.FilePath
import           Test.Tasty
import           Test.Tasty.Golden

-- | .\/Golden\/FstSnd.agda  .\/Golden\/FstSnd_a.golden
-- mkdGoldenTest "FstSnd" "a"
-- mkdGoldenTest "FstSnd" "b"
mkGoldenTest :: String -> Ident -> TestTree
mkGoldenTest modPrefix var = goldenVsString testName goldenPath result
  where
    result = pack <$> compileRunPrint agdap var'
    goldenPath = "Golden" </> modPrefix ++ "_" ++ var <.> "golden"
    var' = modPrefix ++ "." ++ var
    agdap = "Golden" </> modPrefix ++ ".agda"
    testName = modPrefix ++ " " ++ var
