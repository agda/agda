{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE DeriveDataTypeable #-}
-- | Contains all information required to link Agda modules.
--
module Agda.Compiler.UHC.ModuleInfo
  ( AModuleInfo (..)
  , AModuleInterface (..)
  , AConInfo (..)
  , ModVersion
  , ConInstMp
  , currentModInfoVersion
  )
where

import qualified Data.Map as M
import Data.Monoid
import Data.Typeable (Typeable)
import Data.Time.Clock.POSIX

import Agda.Syntax.Internal

import Agda.Compiler.UHC.Naming
import Agda.Compiler.UHC.AuxAST
import Data.Word

-- | Maps constructor names to their actual implementation names.
-- Used for instantiated modules.
type ConInstMp = M.Map QName QName

type ModVersion = POSIXTime

currentModInfoVersion :: Word64
currentModInfoVersion = 20141022 * 10 + 0

data AModuleInfo
  = AModuleInfo
  { amiFileVersion :: Word64
  , amiAgdaVersion :: Word64 -- same version as in Typechecking/Serialise
  , amiModule :: ModuleName
  , amiInterface :: AModuleInterface    -- ^ Contains linking information for the current module (non-transitive).
  , amiVersion :: ModVersion
  , amiDepsVersion :: [(ModuleName, ModVersion)] -- dependency versions for the current module (non-transitive)
  }
  deriving (Show, Typeable)


-- | The interface of a module. Contains all information required to import
-- a module. Needs to be merged with the module interface of all imports
-- of this module to get the actual interface to use.
data AModuleInterface
  = AModuleInterface
  { amifConMp :: M.Map QName AConInfo  -- ^ Maps agda constructor qnames to types/constructor. (accumulating)
  , amifNameMp :: NameMap    -- ^ Maps Agda module-level names to core name. (accumulating)
  , amifConInstMp :: ConInstMp
  }
  deriving (Show, Typeable)

data AConInfo
  = AConInfo
  { aciDataType :: ADataTy
  , aciDataCon :: ADataCon
  }
  deriving (Show, Typeable)

instance Monoid AModuleInterface where
  mempty = AModuleInterface
            { amifConMp = M.empty
            , amifNameMp = mempty
            , amifConInstMp = M.empty
            }
  mappend x y = AModuleInterface
        { amifConMp = amifConMp x `M.union` amifConMp y
        , amifNameMp = amifNameMp x `mappend` amifNameMp y
        , amifConInstMp = amifConInstMp x `M.union` amifConInstMp y
        }
