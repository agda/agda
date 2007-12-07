
module TypeChecking.Rules.Decl where

import Data.Map           (Map)
import Syntax.Info        (ModuleInfo)
import Syntax.Common      (NamedArg, Nat)
import Syntax.Abstract    (QName, Expr, Declaration, ModuleName, Telescope)
import TypeChecking.Monad (TCM)

checkDecls :: [Declaration] -> TCM ()
checkDecl  :: Declaration -> TCM ()
checkSectionApplication' ::
  ModuleInfo -> Nat -> ModuleName -> Telescope -> ModuleName -> [NamedArg Expr] ->
  Map QName QName -> Map ModuleName ModuleName -> TCM ()
