
module Agda.TypeChecking.Rules.Decl where

import Agda.Syntax.Info        (ModuleInfo)
import Agda.Syntax.Abstract    (QName, Declaration, ModuleName, ModuleApplication, ScopeCopyInfo)
import Agda.TypeChecking.Monad (TCM)

checkDecls :: [Declaration] -> TCM ()
checkDecl  :: Declaration -> TCM ()
checkSectionApplication :: ModuleInfo -> ModuleName -> ModuleApplication -> ScopeCopyInfo -> TCM ()
