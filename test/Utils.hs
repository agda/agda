{-# LANGUAGE CPP #-}
module Utils where

import qualified Data.Text as T
import System.FilePath
import System.Exit

#if __GLASGOW_HASKELL__ <= 708
import Control.Applicative ((<$>))
#endif

import System.Environment
import Data.Maybe
import Data.Char
import qualified Data.Set as S
import System.Directory


type ProgramResult = (ExitCode, T.Text, T.Text)

type AgdaArgs = [String]

getEnvAgdaArgs :: IO AgdaArgs
getEnvAgdaArgs = maybe [] words <$> getEnvVar "AGDA_ARGS"


getAgdaBin :: IO FilePath
getAgdaBin = do
  agda <- getEnvVar "AGDA_BIN"
  case agda of
    Just x -> return x
    Nothing -> fail "AGDA_BIN environment variable not set, aborting..."

-- | Gets the program executable. If an environment variable
-- YYY_BIN is defined (with yyy converted to upper case),
-- the value of it is returned. Otherwise, the input value
-- is returned unchanged.
getProg :: String -> IO FilePath
getProg prog = fromMaybe prog <$> getEnvVar (map toUpper prog ++ "_BIN")

getEnvVar :: String -> IO (Maybe String)
getEnvVar v =
  lookup v <$> getEnvironment

agdaExts :: S.Set String
agdaExts = S.fromList [".agda", ".lagda"]

getAgdaFilesInDir :: String -> IO [FilePath]
getAgdaFilesInDir dir = map (dir </>) . filter (flip S.member agdaExts . takeExtension) <$> getDirectoryContents dir

