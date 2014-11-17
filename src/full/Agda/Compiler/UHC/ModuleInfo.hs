-- | Contains all information required to link to this Agda module.
module Agda.Compiler.UHC.ModuleInfo
  ( AModuleInfo (..)
  , AModuleInterface (..)
  , AConInfo (..)
  )
where

import qualified Data.Map as M
import Data.Monoid

import Agda.Syntax.Internal

import Agda.Compiler.UHC.Naming
import Agda.Compiler.UHC.AuxAST

data AModuleInfo
  = AModuleInfo
  { amiModule :: ModuleName
  , amiInterface :: AModuleInterface    -- ^ Contains linking information (transitive).
  , amiCurNameMp :: NameMap    -- ^ NameMap of just the current module.
  }
  deriving (Show)

-- | The interface of a module. Contains all information required to import
-- a module, including information from transitive imports.
data AModuleInterface
  = AModuleInterface
  { amifConMp :: M.Map QName AConInfo  -- ^ Maps agda constructor qnames to types/constructor. (accumulating)
  , amifNameMp :: NameMap    -- ^ Maps Agda module-level names to core name. (accumulating)
  }
  deriving (Show)

data AConInfo
  = AConInfo
  { aciDataType :: ADataTy
  , aciDataCon :: ADataCon
  }
  deriving (Show)

instance Monoid AModuleInterface where
  mempty = AModuleInterface
            { amifConMp = M.empty
            , amifNameMp = mempty
            }
  mappend x y = AModuleInterface
        { amifConMp = amifConMp x `M.union` amifConMp y
        , amifNameMp = amifNameMp x `mappend` amifNameMp y
        }
