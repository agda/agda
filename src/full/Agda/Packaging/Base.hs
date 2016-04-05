{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE MultiWayIf #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Agda.Packaging.Base where

import Data.Text (Text)
import Data.Map (Map)
import Control.Monad
import Data.Maybe
import qualified Data.Map as Map
import Control.Monad.Trans
import System.FilePath
import Data.List
import Data.Version
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BL
import Agda.Utils.Except
import Data.Set (Set)

import Data.Aeson

import Agda.Syntax.Concrete
import Agda.Utils.FileName
import Agda.Utils.Pretty

-- for Version JSON instances, TODO move
import Text.ParserCombinators.ReadP

#include "undefined.h"
import Agda.Utils.Impossible

-- | Hash of the current package name, version + the package keys
-- of all dependencies.
newtype PackageKey = PackageKey { packageKey :: Text }
  deriving (Show, Eq, Ord)

-- | Uniquely identifies a package.
data PackageId = PackageId
  { idKey :: PackageKey
  , idName :: Text
  , idVersion :: Version
  }
  deriving (Show, Eq, Ord)

data Package
  = Package
  { pkgId :: PackageId
  , pkgDependencies :: Set PackageId -- ^ Direct dependencies.
  -- the source of this package
  , pkgSrc :: FilePath
  -- generated doc
  , pkgDoc :: FilePath
  -- .agdai files
  , pkgIfaces :: FilePath
  }
  deriving (Show)

data PkgDB
  = PkgDB
  { dbPath      :: FilePath
  , dbPackages  :: Map PackageId Package
  }
  deriving (Show)

data PkgDBStack
  = PkgDBStack
  { stkDBs :: [PkgDB]
  , stkPkgExposed :: Package -> Bool
  }
  deriving (Show)

emptyPackageDBs :: PkgDBStack
emptyPackageDBs = PkgDBStack [] (const True)


-- | The path of a source file (.agda/.lagda)
data ModulePath
  = PlainPath AbsolutePath
  | InPackage PackageId FilePath
  deriving (Show, Eq, Ord)


isPlainPath :: ModulePath -> Bool
isPlainPath (PlainPath _) = True
isPlainPath (InPackage _ _) = False

getPlainPaths :: [ModulePath] -> [AbsolutePath]
getPlainPaths = map (\(PlainPath x) -> x) . filter isPlainPath

getPackage' :: PackageId -> PkgDBStack -> (PkgDB, Package)
getPackage' key dbs =
  fromMaybe __IMPOSSIBLE__ $ listToMaybe $
    catMaybes [(db,) <$> Map.lookup key (dbPackages db) | db <- stkDBs dbs]

exposedPackages' :: PkgDBStack -> [(PkgDB, Package)]
exposedPackages' dbs = filter (stkPkgExposed dbs . snd) (allPackages' dbs)

allPackages' :: PkgDBStack -> [(PkgDB, Package)]
allPackages' dbs = concatMap (\db -> [(db, pkg) | pkg <- Map.elems (dbPackages db)]) (stkDBs dbs)

-- | Applies an additional filter to a pkg database. Only hides but does *not* remove packages!
filterPkgDBs :: (Package -> Bool) -> PkgDBStack -> PkgDBStack
filterPkgDBs f dbs = dbs { stkPkgExposed = \pkg -> f pkg && (stkPkgExposed dbs pkg)}

findSrc' :: PkgDBStack -> TopLevelModuleName -> IO [ModulePath]
findSrc' dbs mod = do
  r <- forM (exposedPackages' dbs) $ \(db, pkg) -> do
    files <- liftIO $ filterM (\f -> doesFileExistCaseSensitive $ dbPath db </> pkgSrc pkg </> f) fileNames
    case files of
      []  -> return []
      [x] -> return [InPackage (pkgId pkg) x]
      _   -> __IMPOSSIBLE__
  return $ concat r
  where
    fileNames = map (moduleNameToFileName mod) [".agda", ".lagda"]

asAbsolutePath' :: PkgDBStack -> ModulePath -> IO AbsolutePath
asAbsolutePath' _ (PlainPath f) = return f
asAbsolutePath' dbs (InPackage id f) =
  absolute $ dbPath db </> pdir pkg </> f
  where
    (db, pkg) = getPackage' id dbs
    pdir = if | ".agda" `isSuffixOf` f || ".lagda" `isSuffixOf` f -> pkgSrc
              | ".agdai" `isSuffixOf` f -> pkgIfaces
              | otherwise -> __IMPOSSIBLE__


readPackage :: FilePath -> ExceptT String IO Package
readPackage fp = mkExceptT $ eitherDecodeStrict' <$> BS.readFile fp

writePackage :: FilePath -> Package -> IO ()
writePackage fp = BL.writeFile fp . encode


instance FromJSON PackageKey where
  parseJSON v = PackageKey <$> parseJSON v
instance ToJSON PackageKey where
  toJSON = toJSON . packageKey

instance FromJSON PackageId where
  parseJSON (Object v) = PackageId
    <$> v .: "key"
    <*> v .: "name"
    <*> v .: "version"
  parseJSON _ = mzero
instance ToJSON PackageId where
  toJSON p = object [ "key" .= idKey p, "name" .= idName p, "version" .= idVersion p]

instance FromJSON Package where
  parseJSON (Object v) = Package
    <$> v .: "id"
    <*> v .: "dependencies"
    <*> v .: "src"
    <*> v .: "doc"
    <*> v .: "ifaces"
  parseJSON _ = mzero
instance ToJSON Package where
  toJSON p =
    object [ "id" .= pkgId p
           , "dependencies" .= pkgDependencies p
           , "src" .= pkgSrc p, "doc" .= pkgDoc p, "ifaces" .= pkgIfaces p
           ]

instance Pretty PackageKey where
  pretty = pretty . packageKey

instance Pretty PackageId where
  pretty pkg = do
    hcat [ pretty (idName pkg), text "-", pretty (idVersion pkg), text "-", pretty (idKey pkg)]

instance Pretty ModulePath where
  pretty mp = case mp of
    PlainPath f -> pretty f
    InPackage pkg f -> hsep [ pretty pkg, pretty f ]

instance Pretty Version where
  pretty v = text $ showVersion v
