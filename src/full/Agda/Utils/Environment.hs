
-- | Expand environment variables in strings
module Agda.Utils.Environment ( expandEnvironmentVariables ) where

import Data.Char
import Data.Maybe
import System.Environment

expandEnvironmentVariables :: String -> IO String
expandEnvironmentVariables s = do
  env <- getEnvironment
  return $ expandVars env s

expandVars :: [(String, String)] -> String -> String
expandVars env s = concatMap repl $ tokens s
  where
    repl (Var x) = fromMaybe "" $ lookup x env
    repl (Str s) = s

data Token = Var String | Str String
  deriving (Eq, Show)

tokens :: String -> [Token]
tokens s =
  case s of
    '$' : '$' : s -> cons '$' $ tokens s
    '$' : s@(c : _) | isAlpha c -> Var x : tokens s'
      where (x, s') = span isAlphaNum s
    '$' : '{' : s ->
      case break (== '}') s of
        (x, '}' : s) -> Var x : tokens s
        _            -> [Str $ "${" ++ s] -- abort on unterminated '{'
    c : s -> cons c $ tokens s
    ""    -> []
  where
    cons c (Str s : ts) = Str (c : s) : ts
    cons c ts           = Str [c] : ts

