
module Agda.TypeChecking.Rules.Decl where

import Agda.Syntax.Info        (ModuleInfo)
import Agda.Syntax.Abstract    (QName, Declaration, ModuleName, ModuleApplication, Ren)
import Agda.TypeChecking.Monad (TCM)

checkDecls :: [Declaration] -> TCM ()
checkDecl  :: Declaration -> TCM ()
checkSectionApplication ::
  ModuleInfo -> ModuleName -> ModuleApplication ->
  Ren QName -> Ren ModuleName -> TCM ()
