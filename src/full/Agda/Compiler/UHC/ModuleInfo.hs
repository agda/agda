{-# LANGUAGE DeriveDataTypeable #-}
-- | Contains all information required to link to this Agda module.
module Agda.Compiler.UHC.ModuleInfo
  ( AModuleInfo (..)
  , AModuleInterface (..)
  , AConInfo (..)
  , ModVersion
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

type ModVersion = POSIXTime

currentModInfoVersion :: Word64
currentModInfoVersion = 20141022 * 10 + 0

data AModuleInfo
  = AModuleInfo
  { amiFileVersion :: Word64
  , amiAgdaVersion :: Word64 -- same version as in Typechecking/Serialise
  , amiModule :: ModuleName
  , amiInterface :: AModuleInterface    -- ^ Contains linking information (transitive).
  , amiCurNameMp :: NameMap    -- ^ NameMap of just the current module.
  , amiVersion :: ModVersion
  , amiDepsVersion :: [(ModuleName, ModVersion)]
  }
  deriving (Show, Typeable)

-- | The interface of a module. Contains all information required to import
-- a module, including information from transitive imports.
data AModuleInterface
  = AModuleInterface
  { amifConMp :: M.Map QName AConInfo  -- ^ Maps agda constructor qnames to types/constructor. (accumulating)
  , amifNameMp :: NameMap    -- ^ Maps Agda module-level names to core name. (accumulating)
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
            }
  mappend x y = AModuleInterface
        { amifConMp = amifConMp x `M.union` amifConMp y
        , amifNameMp = amifNameMp x `mappend` amifNameMp y
        }
