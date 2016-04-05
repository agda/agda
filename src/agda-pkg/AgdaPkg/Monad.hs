{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
module AgdaPkg.Monad where

import Data.Set (Set)
import qualified Data.Set as Set

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Reader
import Control.Monad.Catch
import Control.Monad.State

import Agda.Packaging.Base

import AgdaPkg.PackageDesc.Base

type PkgM = PkgT IO

data PackageBuildEnv
  = PackageBuildEnv
  { pbePackage :: PackageDesc
  , pbeBuildDir :: FilePath
  , pbePkgDBs :: PkgDBStack
  , pbeAgdaOpts :: [String]
  }


newtype PkgT m a = PkgT { unPkgT :: ReaderT PackageBuildEnv m a}
  deriving (MonadIO, Monad, Applicative, Functor, MonadThrow, MonadCatch, MonadMask)

runPkgT :: PackageBuildEnv -> PkgT m a -> m a
runPkgT e c = runReaderT (unPkgT c) e

class Monad m => MonadPkg m where
  getPackageBuildEnv :: m PackageBuildEnv

instance Monad m => MonadPkg (PkgT m) where
  getPackageBuildEnv = PkgT ask

instance MonadPkg m => MonadPkg (StateT s m) where
  getPackageBuildEnv = lift getPackageBuildEnv

instance MonadPkg m => MonadPkg (ReaderT e m) where
  getPackageBuildEnv = lift getPackageBuildEnv


data BuildDir = WithDir FilePath | TempDir
  deriving (Show)

data GlobalOptions
  = GlobalOptions
  { gAgdaOpts :: [String]
  , gBuildDir :: BuildDir
  , gPkgDBs :: [FilePath]
  , gPkgFilter :: PackageFilter
  }
  deriving (Show)

data PackageFilter
  = PAll
  | PNone -- filter all packages
  | PByPkgId (Set PackageId) -- only expose packages with given ids
  deriving (Show)

data Target = HtmlDoc | LaTeXDoc | CabalPackage
  deriving (Show, Eq, Ord)

type Targets = Set Target


getBuildDir :: MonadPkg m => m FilePath
getBuildDir = pbeBuildDir <$> getPackageBuildEnv

getPkgDBs :: MonadPkg m => m PkgDBStack
getPkgDBs = pbePkgDBs <$> getPackageBuildEnv

getCurrentPackage :: MonadPkg m => m PackageDesc
getCurrentPackage = pbePackage <$> getPackageBuildEnv

getAgdaOptions :: MonadPkg m => m [String]
getAgdaOptions = pbeAgdaOpts <$> getPackageBuildEnv
