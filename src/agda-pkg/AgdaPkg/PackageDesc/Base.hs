{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}
module AgdaPkg.PackageDesc.Base where

import Data.Version
import Data.Text (Text)
import System.FilePath
import Agda.Packaging.Base () -- Version JSON instance, TODO move to Utils
import Control.Monad
import Data.List
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map

import Agda.Utils.Lens

import Data.Aeson

#include "undefined.h"
import Agda.Utils.Impossible

-- project build desc
type PackageName = Text

data PackageDesc
  = PackageDesc
  { pLocation :: FilePath
  , pName :: PackageName
  , pVersion :: Version
  , pComponents :: [Component]
  }
  deriving (Show)

data Component
  = Library
  { cBuildInfo :: BuildInfo
  }
  | Executable
  { cBuildInfo :: BuildInfo
  }
  deriving (Show)

isLibrary :: Component -> Bool
isLibrary (Library{}) = True
isLibrary _ = False

data BuildInfo
  = BuildInfo
  { bSrcDirs :: [FilePath]

  , bDependencies :: Dependencies
  , bAgdaOptions :: [String]
  }
  deriving (Show)

type AgdaDependencies = Map PackageName VersionConstraint
type HsDependencies = Map PackageName VersionConstraint

data Dependencies
  = Dependencies
  { dAgdaDependencies :: AgdaDependencies
  , dHsDependencies :: HsDependencies
  }
  deriving (Show)

instance Monoid Dependencies where
  mappend (Dependencies a1 a2) (Dependencies b1 b2)
    = Dependencies (f a1 b1) (f a2 b2)
    where f = Map.unionWith (\x y -> VAnd [x, y])
  mempty = Dependencies Map.empty Map.empty

data VersionConstraint
  = VAny
  | VExactly Version
  | VAnd [VersionConstraint]
--  | LessThan Version
--  | Not VersionConstraint
--  | And [VersionConstraint]
--  | Or [VersionConstraint
  deriving (Show)


instance FromJSON PackageDesc where
  parseJSON (Object v) = PackageDesc __IMPOSSIBLE__
    <$> v .: "name"
    <*> v .: "version"
    -- handle all components
    <*> ((\x -> [Library x]) <$> (parseJSON =<< (v .: "library")))
  parseJSON _ = mzero

instance FromJSON BuildInfo where
  parseJSON (Object v) = BuildInfo
    <$> v .: "source-dirs"
    <*> parseJSON (Object v)
    <*> v .: "agda-options"
  parseJSON _ = mzero

instance FromJSON Dependencies where
  parseJSON (Object v) = (\a b -> Dependencies (f a) (f b))
    <$> v .: "agda-dependencies"
    <*> v .: "hs-dependencies"
    where f = Map.fromList . flip zip (repeat VAny)
  parseJSON _ = mzero


library :: Lens' (Maybe Component) PackageDesc
library f s =
  f (find isLibrary $ pComponents s) <&>
  \x -> s { pComponents = (filter (not . isLibrary) $ pComponents s) ++ maybeToList x }

library' :: Lens' Component PackageDesc
library' f s =
  f (fromMaybe __IMPOSSIBLE__ $ find isLibrary $ pComponents s) <&>
  \x -> s { pComponents = (filter (not . isLibrary) $ pComponents s) ++ [x] }

components :: Lens' [Component] PackageDesc
components f s =
  f (pComponents s) <&>
  \x -> s { pComponents = x }

buildInfo :: Lens' BuildInfo Component
buildInfo f s =
  f (cBuildInfo s) <&>
  \x -> s { cBuildInfo = x }

dependencies :: Lens' Dependencies BuildInfo
dependencies f s =
  f (bDependencies s) <&>
  \x -> s { bDependencies = x }

agdaDependencies :: Lens' AgdaDependencies Dependencies
agdaDependencies f s =
  f (dAgdaDependencies s) <&>
  \x -> s { dAgdaDependencies = x}

hsDependencies :: Lens' HsDependencies Dependencies
hsDependencies f s =
  f (dHsDependencies s) <&>
  \x -> s { dHsDependencies = x}
