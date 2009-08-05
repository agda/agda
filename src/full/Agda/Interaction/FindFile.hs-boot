module Agda.Interaction.FindFile where

import Data.Map (Map)
import Agda.Syntax.Concrete.Name (TopLevelModuleName)

type ModuleToSource = Map TopLevelModuleName FilePath
