{-# LANGUAGE DeriveGeneric #-}

module Agda.Version
  ( version
  , package
  ) where

import GHC.Generics ( Generic, Rep, packageName )
import Data.List ( intercalate )
import Data.Version ( Version(versionBranch) )

import qualified Paths_Agda as PA

-- | The version of Agda.

version :: String
version = intercalate "." $ map show $
            versionBranch PA.version

-- | This package name.
-- This is mainly intended for use in the test suites to filter ephemeral
-- hash-fingerprinted package names like @Agda-2.6.2-5ceeWeguf1QFMaHLput4zw@.

package :: String
package = packageName (undefined :: Rep AnArbitrarySymbolInThisPackage p)

data AnArbitrarySymbolInThisPackage deriving Generic
