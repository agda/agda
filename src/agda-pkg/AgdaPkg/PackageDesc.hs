{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE OverloadedStrings #-}
module AgdaPkg.PackageDesc
  ( module AgdaPkg.PackageDesc
  , module AgdaPkg.PackageDesc.Base
  )
where

import Data.Version
import Data.Text (Text)
import System.FilePath
import qualified Data.ByteString as BS
import Control.Monad.Trans
import Control.Monad.Catch
import qualified Data.Map as Map

import Data.Yaml

import Agda.Utils.Either
import Agda.Utils.Lens

import AgdaPkg.PackageDesc.Base
import AgdaPkg.Monad
import AgdaPkg.Error

parsePackageDesc :: (MonadThrow m, MonadIO m) => FilePath -> m PackageDesc
parsePackageDesc fp = do
  caseEitherM (liftIO $ decodeFileEither fp)
    (throwM . PackageParseError . prettyPrintParseException)
    (\x -> return $ x { pLocation = takeDirectory fp })

addDefaultDependencies :: PackageDesc -> PackageDesc
addDefaultDependencies desc = do
  over components (map
    (over (buildInfo . dependencies) (mappend depsToAdd)))
            desc
  where
    -- deps for all packages, including Agda-Primitives itself.
    veryPrimDeps = set hsDependencies (Map.fromList
      [("text", VAny)]) mempty
    -- deps for all other packages
    primDeps = veryPrimDeps `mappend` set agdaDependencies (Map.singleton "Agda-Primitives" VAny) mempty
    depsToAdd = if (pName desc == "Agda-Primitives") then veryPrimDeps else primDeps


readPackageDesc :: (MonadThrow m, MonadIO m) => FilePath -> m PackageDesc
readPackageDesc fp = addDefaultDependencies <$> parsePackageDesc fp
