module Agda.TypeChecking.Rules.Def where

import Agda.Syntax.Abstract
import Agda.Syntax.Info
import Agda.TypeChecking.Monad

checkFunDef :: Delayed -> DefInfo -> QName -> [Clause] -> TCM ()
