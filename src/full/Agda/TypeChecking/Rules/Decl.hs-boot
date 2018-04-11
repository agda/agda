
module Agda.TypeChecking.Rules.Decl where

import Agda.Syntax.Info (ModuleInfo)
import Agda.Syntax.Abstract
import Agda.TypeChecking.Monad.Base (TCM)

checkDecls :: [Declaration] -> TCM ()
checkDecl  :: Declaration -> TCM ()
checkSectionApplication :: ModuleInfo -> ModuleName -> ModuleApplication -> ScopeCopyInfo -> TCM ()
