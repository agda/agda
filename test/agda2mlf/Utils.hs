module Utils where

import qualified Data.ByteString.Lazy.Char8    as B
import           System.FilePath
import           Test.Tasty
import           Test.Tasty.Golden

import           Agda.Compiler.Malfunction.AST
import           Agda.Compiler.Malfunction.Run
import           Data.Either
import           Data.Either.Extra


-- | .\/Golden\/FstSnd.agda  .\/Golden\/FstSnd_a.golden
-- mkdGoldenTest "FstSnd" "a"
-- mkdGoldenTest "FstSnd" "b"
mkGoldenTest :: String -> (Either String Ident) -> TestTree
mkGoldenTest modPrefix testId = goldenVsString testName goldenPath result
  where
    testIdStr = fromEither testId
    result = case testId of
      Left str -> B.pack <$> compileRun agdap
      Right var -> B.pack <$> compileRunPrint agdap var'
    goldenPath = "Golden" </> modPrefix ++ "_" ++ testIdStr <.> "golden"
    var' = modPrefix ++ "." ++ testIdStr
    agdap = "Golden" </> modPrefix ++ ".agda"
    testName = modPrefix ++ " " ++ testIdStr

mkGoldenGroup :: String -> [Ident] -> TestTree
mkGoldenGroup modPrefix vars = testGroup modPrefix
  (map (mkGoldenTest modPrefix) (map Right vars))
