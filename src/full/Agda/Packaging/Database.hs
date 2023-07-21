{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.Packaging.Database where
-- FIXME: proper exports
{-
-- Standard Library Imports
import           Control.Applicative
import qualified Control.Exception
import           Control.Monad.Cont
import           Control.Monad.Error
import           Data.List
  ( foldl'
  , intersperse
  , isSuffixOf
  , partition )
import           Data.Maybe
  ( fromJust )
import           System.Directory
  ( createDirectoryIfMissing
  , getAppUserDataDirectory
  , getDirectoryContents
  , removeFile )
import           System.FilePath
import           System.IO
  ( IOMode (ReadMode)
  , hGetContents
  , hSetEncoding
  , openFile
  , utf8 )
import           System.IO.Error
  ( isPermissionError
  , try )

-- External Library Imports
import qualified Distribution.InstalledPackageInfo
  as Cabal
    ( InstalledPackageInfo
    , exposed
    , exposedModules
    , depends
    , hiddenModules
    , installedPackageId
    , parseInstalledPackageInfo
    , showInstalledPackageInfo )
import qualified Distribution.Package
  as Cabal
    ( PackageIdentifier
    , packageId )
import qualified Distribution.ParseUtils
  as Cabal
    ( ParseResult (..)
    , locatedErrorMsg )
import qualified Distribution.Simple.Utils
  as Cabal
    ( die
    , writeUTF8File )
import qualified Distribution.Text
  as Cabal
    ( display
    , simpleParse )

-- Local Imports
import Agda.Packaging.Config
import Agda.Packaging.Monad
import Agda.Packaging.Types
import Paths_Agda
  ( getDataDir )

-------------------------------------------------------------------------------

--------------------------
-- Getting the DB paths --
--------------------------

getPkgDBPathGlobal :: IO FilePath
getPkgDBPathGlobal = do
  result <- try action
  case result of
    Left  ioErr    -> Cabal.die $ show ioErr
    Right filePath -> return filePath
  where
    action =  pure (</>)
          <*> getDataDir
          <*> pure "package.conf.d"

getPkgDBPathUser :: IO FilePath
getPkgDBPathUser = do
  result <- try action
  case result of
    Left  ioErr    -> Cabal.die $ show ioErr
    Right filePath -> return filePath
  where
    action =  pure (</>)
          <*> getAppUserDataDirectory "Agda"
          <*> pure "package.conf.d"



---------------------------------
-- Loading the DBs into memory --
---------------------------------

getPkgDBs :: [FilePath] -> IO PackageDBStack
getPkgDBs givenPkgDBNames = do
  pkgDBNames <-
    -- If no package databases are specified, default to getting the
    -- global and user packages.
    if null givenPkgDBNames
    then
          pure (\ db1 db2 -> db1 : db2 : [])
      <*> getPkgDBPathGlobal
      <*> getPkgDBPathUser
    else
      return givenPkgDBNames
  mapM readParsePkgDB pkgDBNames

readParsePkgDB :: PackageDBName -> IO NamedPackageDB
readParsePkgDB dbName = do
  result <- try $ getDirectoryContents dbName
  case result of
    Left  ioErr     -> Cabal.die $ show ioErr
    Right filePaths -> do
      pkgInfos <- mapM parseSingletonPkgConf $ map (dbName </>) dbEntries
      return $ NamedPackageDB
        { dbName = dbName
        , db     = pkgInfos }
      where
        dbEntries = filter (".conf" `isSuffixOf`) filePaths

parseSingletonPkgConf :: FilePath -> IO Cabal.InstalledPackageInfo
parseSingletonPkgConf = (parsePkgInfo =<<) . readUTF8File
  where
    readUTF8File :: FilePath -> IO String
    readUTF8File file = do
      handle <- openFile file ReadMode
      hSetEncoding handle utf8
      hGetContents handle

parsePkgInfo :: String -> IO Cabal.InstalledPackageInfo
parsePkgInfo pkgInfoStr =
  case Cabal.parseInstalledPackageInfo pkgInfoStr of
    Cabal.ParseOk     warnings pkgInfo ->
      return pkgInfo
    Cabal.ParseFailed err              ->
      case Cabal.locatedErrorMsg err of
        (Nothing     , msg) -> Cabal.die msg
        (Just  lineNo, msg) -> Cabal.die (show lineNo ++ ": " ++ msg)


-------------------
-- DB operations --
-------------------

data DBOp
  = PkgAdd    Cabal.InstalledPackageInfo
  | PkgModify Cabal.InstalledPackageInfo
  | PkgRemove Cabal.InstalledPackageInfo


----------------------------------
-- Processing the DBs in memory --
----------------------------------

brokenPkgs :: PackageDB -> PackageDB
brokenPkgs = snd . transClos []
  where
    -- Calculate the transitive closure of 'ok' packages, i.e.,
    -- packages with all of their dependencies available.
    transClos :: PackageDB -> PackageDB -> (PackageDB, PackageDB)
    transClos okPkgs pkgs =
      case partition (ok okPkgs) pkgs of
        ([]     , pkgs') -> (okPkgs, pkgs')
        (okPkgs', pkgs') -> transClos (okPkgs' ++ okPkgs) pkgs'
      where
        -- A package is 'ok' with respect to a package database if the
        -- packages dependencies are available in the database.
        ok :: PackageDB -> Cabal.InstalledPackageInfo -> Bool
        ok okPkgs pkg = null dangling
          where
            dangling = filter (`notElem` pkgIds) (Cabal.depends pkg)
            pkgIds   = map Cabal.installedPackageId okPkgs

flattenPkgDBs :: PackageDBStack -> PackageDB
flattenPkgDBs = concatMap db

modifyDBWithOps :: PackageDB -> [DBOp] -> PackageDB
modifyDBWithOps pkgDB dbOps = foldl' applyOp pkgDB dbOps
  where
    applyOp :: PackageDB -> DBOp -> PackageDB
    applyOp pkgInfos (PkgAdd    pkgInfo) = pkgInfo : pkgInfos
    applyOp pkgInfos (PkgModify pkgInfo) = applyOp pkgDB' $ PkgAdd pkgInfo
      where
        pkgDB' = applyOp pkgInfos $ PkgRemove pkgInfo
    applyOp pkgInfos (PkgRemove pkgInfo) = filter fpred pkgInfos
      where
        fpred  = (Cabal.installedPackageId pkgInfo /=)
               .  Cabal.installedPackageId


-------------------------------
-- Modifying the DBs on disk --
-------------------------------

modifyAndWriteDBWithOps :: NamedPackageDB -> [DBOp] -> IO ()
modifyAndWriteDBWithOps npkgDB dbOps = do
  createDirectoryIfMissing True $ dbName npkgDB
  writeDBWithOps npkgDB{ db = db' } dbOps
  where
    db' = db npkgDB `modifyDBWithOps` dbOps

writeDBWithOps :: NamedPackageDB -> [DBOp] -> IO ()
writeDBWithOps npkgDB = mapM_ doOp
  where
    fileNameOf      pkgInfo  =  dbName npkgDB
                            </> Cabal.display (Cabal.installedPackageId pkgInfo)
                            <.> "conf"

    doOp (PkgAdd    pkgInfo) = Cabal.writeUTF8File (fileNameOf pkgInfo)
                             $ Cabal.showInstalledPackageInfo  pkgInfo
    doOp (PkgModify pkgInfo) = doOp                   $ PkgAdd pkgInfo
    doOp (PkgRemove pkgInfo) = removeFile          (fileNameOf pkgInfo)

modifyPkgInfoAndWriteDBWithFun :: Cabal.PackageIdentifier
                               -> (Cabal.InstalledPackageInfo -> DBOp)
                               -> AgdaPkg opt ()
modifyPkgInfoAndWriteDBWithFun pkgId funToOp = asksM (rec . configPkgDBStack)
  where
    rec :: PackageDBStack -> AgdaPkg opt ()
    rec = liftIO . mapM_ (\ npkgDB -> modifyAndWriteDBWithOps npkgDB (generateOps $ db npkgDB))
      where
        generateOps :: PackageDB -> [DBOp]
        generateOps []                       = []
        generateOps (pkgInfo:pkgInfos)
          | Cabal.packageId pkgInfo == pkgId = funToOp pkgInfo : generateOps pkgInfos
          | otherwise                        =                   generateOps pkgInfos
-}
