{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.Rules.Decl where

import Agda.Syntax.Info (ModuleInfo)
import Agda.Syntax.Abstract
import Agda.Syntax.Common
import Agda.Syntax.Scope.Base
import Agda.TypeChecking.Monad.Base (TCM)

checkDecls :: [Declaration] -> TCM ()
checkDecl  :: Declaration -> TCM ()
checkSig   :: KindOfName -> DefInfo -> Erased -> QName ->
              GeneralizeTelescope -> Expr -> TCM ()
checkSectionApplication ::
  ModuleInfo -> Erased -> ModuleName -> ModuleApplication ->
  ScopeCopyInfo -> ImportDirective -> TCM ()
