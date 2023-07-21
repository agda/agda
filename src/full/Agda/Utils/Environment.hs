{-# OPTIONS_GHC -Wunused-imports #-}

-- | Expand environment variables in strings
module Agda.Utils.Environment ( expandEnvironmentVariables ) where

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
  -> [(String, String)]  -- ^ Environment variable substitution map.
  -> String              -- ^ Input.
  -> String              -- ^ Output with variables and @~@ (home) substituted.
expandVars home env s = concatMap repl $ tokens s
  where
    repl Home    = home ++ "/"
    repl (Var x) = fromMaybe "" $ lookup x env
    repl (Str s) = s

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
