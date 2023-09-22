{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.Syntax.TopLevelModuleName.Boot where

import Agda.Syntax.Common (ModuleNameHash)

import GHC.Generics (Generic)


type TopLevelModuleNameParts = List1 Text

data TopLevelModuleName' range = TopLevelModuleName
  { moduleNameRange :: range
  , moduleNameId    :: {-# UNPACK #-} !ModuleNameHash
  , moduleNameParts :: TopLevelModuleNameParts
  }
  deriving (Show, Generic)
