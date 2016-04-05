{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE MultiWayIf #-}

module Agda.Packaging.Database where

import Data.Text (Text)
import qualified Data.Text as T
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set

import Control.Monad
import Control.Monad.Trans
import System.IO.Error
import Data.Aeson
import System.Directory
import System.FilePath
import Control.Applicative
import Data.Maybe
import Data.List
import qualified Data.ByteString as BS
import Data.Version
import System.Environment

import Paths_Agda

import Agda.Syntax.Concrete
import Agda.Syntax.Concrete.Name
import Agda.Packaging.Base
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Imports
import {-# SOURCE #-} Agda.TypeChecking.Monad.Options
import Agda.Interaction.Options

import Agda.Utils.List
import Agda.Utils.Either
import Agda.Utils.Except
import Agda.Utils.Pretty
import Agda.Utils.FileName

#include "undefined.h"
import Agda.Utils.Impossible

--------------------------
-- Getting the DB paths --
--------------------------

getPkgDBPathGlobal :: MonadIO m => m FilePath
getPkgDBPathGlobal = do
  (</>) <$> liftIO getDataDir <*> pure (showVersion version </> "packages")

getPkgDBPathUser :: MonadIO m => ExceptT String m FilePath
getPkgDBPathUser = do
  result <- liftIO $ tryIOError action
  case result of
    Left  ioErr    -> throwError $ show ioErr
    Right filePath -> return filePath
  where
    action =  pure (</>)
          <*> getAppUserDataDirectory "Agda"
          <*> pure (showVersion version </> "packages")

packageDBPath :: MonadIO m => FilePath -> ExceptT String m FilePath
packageDBPath db = case db of
  "__GLOBAL_DB__" -> do
    getPkgDBPathGlobal
  "__USER_DB__"   -> do
    getPkgDBPathUser
  _ -> return db


---------------------------------
-- Loading the DBs into memory --
---------------------------------

readPkgDB :: FilePath -> ExceptT String IO PkgDB
readPkgDB db = do
  db <- packageDBPath db
  pkgs <- do
    isDir <- liftIO $ doesDirectoryExist db
    if not isDir then do
--      reportSLn "pkgs.load" 1 $ "Ignoring invalid package db: " ++ db
      return []
    else do
      fs <- filter (".apkg" `isSuffixOf`) <$> (liftIO $ getDirectoryContents db)

      forM fs $ \f -> do
        readPackage (db </> f)

  return $ PkgDB
    { dbPath = db
    , dbPackages = Map.fromList [ (pkgId p, p) | p <- pkgs]
    }

exceptTToTCM :: ExceptT String IO a -> TCM a
exceptTToTCM e = do
  caseEitherM (liftIO $ runExceptT e) genericError return

loadPkgDBs :: TCM ()
loadPkgDBs = do
  reportSLn "pkgs.load" 1 "Loading package dbs..."

  optDBs <- optPkgDBs <$> liftTCM commandLineOptions
  envDBs <- wordsBy (==':') . fromMaybe "" . lookup "AGDA_PACKAGE_PATH" <$> liftIO getEnvironment

  let dbs = optDBs ++ envDBs
      -- If no package databases are specified, default to getting the
      -- global packages.
      dbs' = if null dbs then ["__GLOBAL_DB__"] else dbs

  loadPkgDBs' dbs'

loadPkgDBs' :: [String] -> TCM ()
loadPkgDBs' fs = do

  dbStk <- PkgDBStack
    <$> mapM (exceptTToTCM  . readPkgDB) fs
    <*> exposedPackagesFilter

  setPackageDBs dbStk
  reportSLn "pkgs.load" 10 "Successfully loaded package dbs."
  reportSDoc "pkgs.load" 50 $ return $
    text "All packages:" <+>
      prettyList (map (pretty . pkgId . snd) $ allPackages' dbStk)
  reportSDoc "pkgs.load" 50 $ return $
    text "Exposed packages:" <+>
      prettyList (map (pretty . pkgId . snd) $ exposedPackages' dbStk)
  where
    exposedPackagesFilter :: TCM (Package -> Bool)
    exposedPackagesFilter = do
      hidePrim <- optHidePrimPkg <$> commandLineOptions
      exposeAll <- optExposeAll <$> commandLineOptions
      exposedKeys <- Set.fromList . map (PackageKey . T.pack) . optExposePkgKeys <$> commandLineOptions
      return $ \pkg ->
        if | idName (pkgId pkg) == "Agda-Primitives" -> not hidePrim
           | exposeAll -> True
           | otherwise -> (idKey (pkgId pkg) `Set.member` exposedKeys)


getPackage :: PackageId -> TCM Package
getPackage pkgId =
  snd . getPackage' pkgId <$> getPackageDBs

getPrimitivesPackage :: TCM (Maybe Package)
getPrimitivesPackage = do
  -- we ignore the exposed/hidden status when looking for the primitive package
  (_, pkgs) <- unzip . allPackages' <$> getPackageDBs
  return $ headMaybe $ filter (("Agda-Primitives" ==). idName . pkgId) pkgs

asAbsolutePath :: ModulePath -> TCM AbsolutePath
asAbsolutePath mp = do
  dbs <- getPackageDBs
  liftIO $ asAbsolutePath' dbs mp

findSrc :: TopLevelModuleName -> TCM [ModulePath]
findSrc m = do
  dbs <- getPackageDBs
  liftIO $ findSrc' dbs m

withExposedPackages :: (Package -> Bool) -> TCM a -> TCM a
withExposedPackages f cont = do
  dbs <- getPackageDBs
  setPackageDBs $ dbs { stkPkgExposed = f }
  r <- cont
  setPackageDBs dbs
  return r
