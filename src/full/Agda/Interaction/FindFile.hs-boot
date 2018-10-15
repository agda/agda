module Agda.Interaction.FindFile where

import Agda.Syntax.Concrete (Module)
import Agda.Syntax.Concrete.Name (TopLevelModuleName)
import Agda.TypeChecking.Monad.Base (TCM)
import Agda.Utils.FileName (AbsolutePath)

moduleName :: AbsolutePath -> Module -> TCM TopLevelModuleName
checkModuleName :: TopLevelModuleName -> AbsolutePath -> Maybe TopLevelModuleName -> TCM ()
