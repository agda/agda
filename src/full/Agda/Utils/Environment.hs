{-# OPTIONS_GHC -Wunused-imports #-}

-- | Expand environment variables in strings
module Agda.Utils.Environment
  ( EnvVars
  , expandEnvironmentVariables
  , expandEnvVarTelescope
  ) where

import Data.Char
import Data.Maybe
import System.Environment
import System.Directory ( getHomeDirectory )

expandEnvironmentVariables :: String -> IO String
expandEnvironmentVariables s = do
  env  <- getEnvironment
  home <- getHomeDirectory
  return $ expandVars home env s

expandVars
  :: String              -- ^ Home directory.
  -> EnvVars             -- ^ Environment variable substitution map.
  -> String              -- ^ Input.
  -> String              -- ^ Output with variables and @~@ (home) substituted.
expandVars home env s = concatMap repl $ tokens s
  where
    repl Home    = home ++ "/"
    repl (Var x) = fromMaybe "" $ lookup x env
    repl (Str s) = s

-- | List of environment variable bindings.
type EnvVars = [(String, String)]

-- | Expand a telescope of environment variables
--   (each value may refer to variables earlier in the list).
expandEnvVarTelescope :: String -> EnvVars -> EnvVars
expandEnvVarTelescope home = reverse . foldl  -- foldl reverses, so re-reverse afterwards
  (\ acc (var, val) -> (var, expandVars home acc val) : acc) []

-- | Tokenization for environment variable substitution.
data Token
  = Home        -- ^ @~@.
  | Var String  -- ^ @$VARIABLE@ or @${VARIABLE}$.
  | Str String  -- ^ Ordinary characters.
  deriving (Eq, Show)

-- | Tokenize a string.
--   The @~@ is recognized as @$HOME@ only at the beginning of the string.
tokens :: String -> [Token]
tokens = \case
  '~'  : '/' : s -> Home : tokens' s
  '\\' : '~' : s -> cons '~' $ tokens' s
  s -> tokens' s
  where
    tokens' :: String -> [Token]
    tokens' = \case
        '$' : '$' : s -> cons '$' $ tokens' s
        '$' : s@(c : _) | c == '_' || isAlpha c -> Var x : tokens' s'
          where
          (x, s') = span (\ c -> c == '_' || isAlphaNum c) s
        '$' : '{' : s ->
          case break (== '}') s of
            (x, '}' : s) -> Var x : tokens' s
            _            -> [Str $ "${" ++ s] -- abort on unterminated '{'
        c : s -> cons c $ tokens' s
        ""    -> []
    cons :: Char -> [Token] -> [Token]
    cons c (Str s : ts) = Str (c : s) : ts
    cons c ts           = Str [c] : ts
