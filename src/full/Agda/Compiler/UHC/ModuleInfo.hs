{-# LANGUAGE CPP                #-}
{-# LANGUAGE DeriveDataTypeable #-}

-- | Contains all information required to link Agda modules.
--
module Agda.Compiler.UHC.ModuleInfo
  ( AModuleInfo (..)
  , ModVersion
  , currentModInfoVersion
  )
where

import qualified Data.Map as M

#if __GLASGOW_HASKELL__ <= 708
import Data.Monoid
#endif

import Data.Typeable (Typeable)

import Agda.Syntax.Internal

import Data.Word

type ModVersion = Integer

currentModInfoVersion :: Word64
currentModInfoVersion = 20150625 * 10 + 0

data AModuleInfo
  = AModuleInfo
  { amiFileVersion :: Word64    -- ^ We don't explicitly store the agda interface version, but this is done by the EmbPrj
                                -- serialization for us. If we were to not use EmbPrj anymore, the
                                -- Agda interface version would need to be stored explicitly!
  , amiModule :: ModuleName
  , amiVersion :: ModVersion
  , amiDepsVersion :: [(ModuleName, ModVersion)] -- dependency versions for the current module (non-transitive)
  }
  deriving (Show, Typeable)

