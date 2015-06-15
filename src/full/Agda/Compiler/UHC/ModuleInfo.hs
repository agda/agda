-- GHC 7.4.2 requires this layout for the pragmas. See Issue 1460.
{-# LANGUAGE CPP,
             DeriveDataTypeable #-}

-- GHC 7.4.2 requires the OPTIONS_GHC pragma(s) after the LANGUAGE
-- pragma(s). See Issue 1460.
{-# OPTIONS_GHC -Wall #-}

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

#if __GLASGOW_HASKELL__ <= 708
import Data.Monoid
#endif

import Data.Typeable (Typeable)

import Agda.Syntax.Internal

import Agda.Compiler.UHC.Naming
import Agda.Compiler.UHC.AuxAST
import Data.Word

-- | Maps constructor names to their actual implementation names.
-- Used for instantiated modules, where datatype definitions gets duplicated,
-- but we want to use the original definition when compiling.
type ConInstMp = M.Map QName QName

type ModVersion = Integer

currentModInfoVersion :: Word64
currentModInfoVersion = 20150323 * 10 + 0

data AModuleInfo
  = AModuleInfo
  { amiFileVersion :: Word64    -- ^ We don't explicitly store the agda interface version, but this is done by the EmbPrj
                                -- serialization for us. If we were to not use EmbPrj anymore, the
                                -- Agda interface version would need to be stored explicitly!
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
  { amifConMp :: M.Map QName AConInfo  -- ^ Maps agda constructor qnames to types/constructor.
  , amifNameMp :: NameMap    -- ^ Maps Agda module-level names to core name.
  , amifConInstMp :: ConInstMp -- ^ Constructor instantiation map.
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
