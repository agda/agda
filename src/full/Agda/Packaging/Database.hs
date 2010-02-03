module Agda.Packaging.Database where
-- FIXME: proper exports

-- Standard Library Imports
import           Control.Applicative
import qualified Control.Exception
import           Control.Monad.Cont
import           Control.Monad.Error
import           Data.List
  ( intersperse
  , partition )
import           Data.Maybe
  ( fromJust )
import           System.Directory
  ( getAppUserDataDirectory )
import           System.FilePath
import           System.IO.Error
  ( isPermissionError )

-- External Library Imports
import qualified Distribution.InstalledPackageInfo
  as Cabal
    ( InstalledPackageInfo
    , exposedModules
    , depends
    , hiddenModules
    , installedPackageId )
import qualified Distribution.Package
  as Cabal
    ( PackageIdentifier
    , packageId )
import qualified Distribution.Simple.Utils
  as Cabal
    ( die
    , withFileContents
    , writeFileAtomic )
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

-- FIXME: Error handling
getPkgDBPathGlobal :: IO FilePath
getPkgDBPathGlobal =  pure (</>)
                  <*> getDataDir
                  <*> pure "package.conf"

-- FIXME: Error handling
getPkgDBPathUser :: IO FilePath
getPkgDBPathUser =  pure (</>)
                <*> getAppUserDataDirectory "Agda"
                <*> pure "package.conf"

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

-- FIXME: Error handling
readParsePkgDB :: PackageDBName -> IO NamedPackageDB
readParsePkgDB dbName = do
  (parsePkgDB =<< readFile dbName)
    `catch` ioError
  where
    parsePkgDB :: String -> IO NamedPackageDB
    parsePkgDB pkgDBText = do
      let db = map parsePkgInfo $ read pkgDBText
      return $ NamedPackageDB { dbName = dbName, db = db }
        where
          parsePkgInfo pkgInfo = pkgInfo
            { Cabal.exposedModules = map parse $ Cabal.exposedModules pkgInfo
            , Cabal.hiddenModules  = map parse $ Cabal.hiddenModules  pkgInfo }
            where
              parse = fromJust . Cabal.simpleParse

collatePkgDBs :: PackageDBStack -> PackageDB
collatePkgDBs = concatMap db

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

-- FIXME: need an elegant way to warn about freshly broken pages
-- before writing to the disk.  Should be able to calculate this
-- somehow by comparing against configOrigBroken.
writePkgDBToFile :: PackageDB -> FilePath -> AgdaPkg opt ()
writePkgDBToFile pkgDB fileName = do
  liftIO $ Cabal.writeFileAtomic fileName serializedPkgInfos
    `catch` \ e ->
      if isPermissionError e
      then Cabal.die errMsg
      else ioError e
  where
    serializedPkgInfos =
         "["
      ++ concat (intersperse ",\n " (map (show . prepPkgInfo) pkgDB))
      ++ "\n]"
      where
        prepPkgInfo pkgInfo = pkgInfo
          { Cabal.exposedModules = map Cabal.display
                                 $ Cabal.exposedModules pkgInfo
          , Cabal.hiddenModules  = map Cabal.display
                                 $ Cabal.hiddenModules  pkgInfo }
    errMsg =  "insufficient permissions to write package database to `"
           ++ fileName
           ++ "'"

modifyPkgInDB :: Cabal.PackageIdentifier
              -> (Cabal.InstalledPackageInfo -> Cabal.InstalledPackageInfo)
              -> AgdaPkg opt ()
modifyPkgInDB pkgId f = asksM (recOuter . configPkgDBStack)
  where
    recOuter :: PackageDBStack -> AgdaPkg opt ()
    recOuter []     = return ()
    recOuter (d:ds) =
      case recInner (db d) of
        Nothing -> recOuter ds
        Just db -> writePkgDBToFile db (dbName d)
      where
        recInner :: PackageDB -> Maybe PackageDB
        recInner []                    = Nothing
        recInner (p:ps)
          | Cabal.packageId p == pkgId = pure (f p : ps)
          | otherwise                  = pure (:) <*> pure p <*> recInner ps
