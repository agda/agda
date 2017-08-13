module Agda.Version where

import Data.Version
import Data.List ( intercalate, map )

import qualified Paths_Agda as PA

-- | The version of Agda.

version :: String
version = intercalate "." $ map show $
            versionBranch PA.version
