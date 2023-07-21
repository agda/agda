{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.Version
  ( version
  , package
  , docsUrl
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

-- | Returns a URL corresponding to the given section in the documentation for
-- the current version.
docsUrl :: String -> String
docsUrl section = "https://agda.readthedocs.io/en/v" ++ version ++ "/" ++ section

data AnArbitrarySymbolInThisPackage deriving Generic
