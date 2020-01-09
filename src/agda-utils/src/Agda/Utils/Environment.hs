
-- | Expand environment variables in strings
module Agda.Utils.Environment ( expandEnvironmentVariables ) where

import Data.Char
import Data.Maybe
import System.Environment
import System.Directory ( getHomeDirectory )

expandEnvironmentVariables :: String -> IO String
expandEnvironmentVariables s = do
  env <- getEnvironment
  home <- getHomeDirectory
  return $ expandVars home env s

expandVars :: String -> [(String, String)] -> String -> String
expandVars home env s = concatMap repl $ tokens s
  where
    repl Home = home ++ "/"
    repl (Var x) = fromMaybe "" $ lookup x env
    repl (Str s) = s

data Token = Home | Var String | Str String
  deriving (Eq, Show)

tokens :: String -> [Token]
tokens s = case s of
  '~' : '/' : s -> Home : tokens' s
  '\\' : '~' : s -> cons '~' $ tokens' s
  _ -> tokens' s
  where
    tokens' :: String -> [Token]
    tokens' s =
      case s of
        '$' : '$' : s -> cons '$' $ tokens' s
        '$' : s@(c : _) | c == '_' || isAlpha c -> Var x : tokens' s'
          where (x, s') = span (\ c -> c == '_' || isAlphaNum c) s
        '$' : '{' : s ->
          case break (== '}') s of
            (x, '}' : s) -> Var x : tokens' s
            _            -> [Str $ "${" ++ s] -- abort on unterminated '{'
        c : s -> cons c $ tokens' s
        ""    -> []
    cons c (Str s : ts) = Str (c : s) : ts
    cons c ts           = Str [c] : ts

