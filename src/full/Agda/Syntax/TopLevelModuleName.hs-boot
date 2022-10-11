module Agda.Syntax.TopLevelModuleName where

import Control.DeepSeq

import {-# SOURCE #-} Agda.Syntax.Position (KillRange)

data TopLevelModuleName

instance Eq        TopLevelModuleName
instance Ord       TopLevelModuleName
instance Show      TopLevelModuleName
instance NFData    TopLevelModuleName
instance KillRange TopLevelModuleName
