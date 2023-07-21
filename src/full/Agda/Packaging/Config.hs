{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.Packaging.Config where
-- FIXME: proper exports

{-
-- External Library Imports
import qualified Distribution.InstalledPackageInfo
  as Cabal
    ( InstalledPackageInfo )

-- Local Library Imports
import Agda.Packaging.Types

--------------------------------------------------------------------------------

-- Parametric in `opt' only so that the environment can be decoupled
-- from the concrete CLI tool
data AgdaPkgConfig opt
  =  AgdaPkgConfig
  { configOpts       :: [opt]
  , configOrigBroken :: [Cabal.InstalledPackageInfo]
  , configPkgDBStack :: [NamedPackageDB]
  , configProgName   :: String }
-}
