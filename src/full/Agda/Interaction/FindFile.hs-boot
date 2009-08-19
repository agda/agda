module Agda.Interaction.FindFile where

import Data.Map (Map)
import Agda.Syntax.Concrete.Name (TopLevelModuleName)
import Agda.Utils.FileName (AbsolutePath)

type ModuleToSource = Map TopLevelModuleName AbsolutePath
