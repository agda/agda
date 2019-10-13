{-# LANGUAGE OverloadedStrings #-}

module ParseConfig
  ( Config(..)
  , parseConfig
  ) where

import Data.Maybe (fromMaybe)
import qualified Data.Yaml as Y
import Data.Yaml (FromJSON(..), (.:?))

data RawConfig = RawConfig
  { __included_dirs  :: Maybe [FilePath]
  , __excluded_dirs  :: Maybe [FilePath]
  , __included_files :: Maybe [FilePath]
  , __excluded_files :: Maybe [FilePath]
  } deriving Show

data Config = Config
  { included_dirs  :: [FilePath]
  , excluded_dirs  :: [FilePath]
  , included_files :: [FilePath]
  , excluded_files :: [FilePath]
  } deriving Show

instance FromJSON RawConfig where
  parseJSON (Y.Object v) =
    RawConfig <$>
    v .:? "included-dirs"  <*>
    v .:? "excluded-dirs"  <*>
    v .:? "included-files" <*>
    v .:? "excluded-files"
  parseJSON _ = fail "Expected Object for Config value"

parseRawConfig :: FilePath -> IO (Either Y.ParseException RawConfig)
parseRawConfig = Y.decodeFileEither

parseConfig :: FilePath -> IO Config
parseConfig fp = do
  result <- Y.decodeFileEither fp
  case result of
    Left _    -> return defaultConfig
    Right cfg -> return $ defaults cfg
  where
    defaults (RawConfig _incDirs _excDirs _incFiles _excFiles) =
      let incDirs  = fromMaybe [] _incDirs
          excDirs  = fromMaybe [] _excDirs
          incFiles = fromMaybe [] _incFiles
          excFiles = fromMaybe [] _excFiles
      in Config incDirs excDirs incFiles excFiles

defaultConfig :: Config
defaultConfig = Config [] [] [] []
