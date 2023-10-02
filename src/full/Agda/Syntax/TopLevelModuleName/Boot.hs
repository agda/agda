{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.Syntax.TopLevelModuleName.Boot where

import Agda.Utils.List1 (List1)
import Agda.Utils.BiMap (HasTag, Tag, tag)

import Control.DeepSeq (NFData, rnf)
import Data.Function (on)
import Data.Hashable (Hashable, hashWithSalt)
import Data.Text (Text)
import Data.Word (Word64)
import GHC.Generics (Generic)

newtype ModuleNameHash = ModuleNameHash { moduleNameHash :: Word64 }
  deriving (Eq, Ord, Hashable)

instance NFData ModuleNameHash where
  rnf _ = ()

instance HasTag ModuleNameHash where
  type Tag ModuleNameHash = ModuleNameHash
  tag = Just . id

noModuleNameHash :: ModuleNameHash
noModuleNameHash = ModuleNameHash 0

-- | The record selector is not included in the resulting strings.

instance Show ModuleNameHash where
  showsPrec p (ModuleNameHash h) = showParen (p > 0) $
    showString "ModuleNameHash " . shows h

type TopLevelModuleNameParts = List1 Text

data TopLevelModuleName' range = TopLevelModuleName
  { moduleNameRange :: range
  , moduleNameId    :: {-# UNPACK #-} !ModuleNameHash
  , moduleNameParts :: TopLevelModuleNameParts
  }
  deriving (Show, Generic)

instance HasTag (TopLevelModuleName' range) where
  type Tag (TopLevelModuleName' range) = ModuleNameHash
  tag = Just . moduleNameId

instance Eq (TopLevelModuleName' range) where
  (==) = (==) `on` moduleNameId

instance Ord (TopLevelModuleName' range) where
  compare = compare `on` moduleNameId

instance Hashable (TopLevelModuleName' range) where
  hashWithSalt salt = hashWithSalt salt . moduleNameId

-- | The 'range' is not forced.

instance NFData (TopLevelModuleName' range) where
  rnf (TopLevelModuleName _ x y) = rnf (x, y)

