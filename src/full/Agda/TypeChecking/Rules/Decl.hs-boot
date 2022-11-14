
module Agda.TypeChecking.Rules.Decl where

import Agda.Syntax.Info (ModuleInfo)
import Agda.Syntax.Abstract
import Agda.Syntax.Scope.Base
import Agda.TypeChecking.Monad.Base (TCM)

checkDecls :: [Declaration] -> TCM ()
checkDecl  :: Declaration -> TCM ()
checkSig   :: KindOfName -> DefInfo -> QName -> GeneralizeTelescope -> Expr -> TCM ()
checkSectionApplication :: ModuleInfo -> ModuleName -> ModuleApplication -> ScopeCopyInfo -> TCM ()
