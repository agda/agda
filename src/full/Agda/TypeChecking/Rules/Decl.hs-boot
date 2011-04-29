
module Agda.TypeChecking.Rules.Decl where

import Data.Map           (Map)
import Agda.Syntax.Info        (ModuleInfo)
import Agda.Syntax.Abstract    (QName, Expr, Declaration, ModuleName, ModuleApplication)
import Agda.TypeChecking.Monad (TCM)

checkDecls :: [Declaration] -> TCM ()
checkDecl  :: Declaration -> TCM ()
checkSectionApplication ::
  ModuleInfo -> ModuleName -> ModuleApplication ->
  Map QName QName -> Map ModuleName ModuleName -> TCM ()
