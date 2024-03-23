{-
A helper module to get repl (ghci) working in Agda
This module is intenionally orphan, it should not be used anywhere outside repl purposes.
-}
module Agda.Repl where
import Agda.Main
import Agda.Compiler.Backend
import Agda.Utils.FileName
import Agda.Interaction.Options.Base
import Data.List (length, elemIndex, take, unlines)
import System.Exit
import Data.Maybe
import qualified Data.Text
import Control.Exception
import Control.Arrow (second)

data TestResult
  = Ok
  | NotOk
  deriving Show

agdaRepl :: (TestResult, FilePath) -> String -> IO ()
agdaRepl (res, fn) opts =
  let idx = (length fn - fromJust (elemIndex '/' (reverse fn)))
      dir = take idx fn
      (Right (_, cliopts), warns) = runOptM $ parseBackendOptions [] (words opts) defaultOptions in
  handle (\(e :: ExitCode) -> if (e == ExitSuccess)
    then case res of
      Ok -> putStrLn "checking ok"
      NotOk -> do
        putStrLn "!!!!!!!! checking ok, but it should not be ok"
        error "abort"
    else case res of
      Ok -> do
        putStrLn "!!!!!!!! checking not ok, but it should be ok"
        error "abort"
      NotOk -> putStrLn "checking not ok") $ runTCMPrettyErrors $
  runAgdaWithOptions
    (defaultInteractor (AbsolutePath (Data.Text.pack fn)))
    "agda"
    (cliopts { optIncludePaths = [dir], optIgnoreAllInterfaces = True })

exec :: FilePath -> String -> IO String
exec fn opts = return $ unlines
  [ ":set +s"
  , ":r"
  , "agdaRepl (Ok, " ++ (show fn) ++ ") " ++ show opts
  ]

tests :: [(TestResult, String)]
tests = map (second ("/Users/knisht/agda/inf/Tests/" ++) )
  [ (Ok, "Test1.agda")
  , (Ok, "Test2.agda")
  , (Ok, "Test3.agda")
  , (Ok, "Test4.agda")
  , (Ok, "Test5.agda")
  , (Ok, "Test6.agda")
  , (Ok, "Test7.agda")
  , (Ok, "Test8.agda")
  , (Ok, "Test9.agda")
  , (Ok, "Test10.agda")
  , (Ok, "Test11.agda")
  , (Ok, "Test12.agda")
  , (Ok, "Test13.agda")
  , (Ok, "Test14.agda")
  , (NotOk, "Test15.agda")
  , (Ok, "Test16.agda")
  , (Ok, "Test17.agda")
  , (Ok, "Test18.agda")
  , (Ok, "Test19.agda")
  , (Ok, "Test20.agda")
  , (NotOk, "Test21.agda")
  , (Ok, "Test22.agda")
  , (NotOk, "Test23.agda")
  , (NotOk, "Test24.agda")
  , (Ok, "Test25.agda")
  , (Ok, "Test26.agda")
  , (Ok, "Test27.agda")
  , (Ok, "Test28.agda")
  , (Ok, "Test29.agda")
  , (Ok, "Test30.agda")
  , (Ok, "Test31.agda")
  , (Ok, "Test32.agda")
  , (NotOk, "Test33.agda")
  , (NotOk, "Test34.agda")
  , (NotOk, "Test35.agda")
  ]

execTests :: IO [()]
execTests = traverse (flip agdaRepl "") tests
