module Agda.TypeChecking.Rules.Def where

import Agda.Syntax.Abstract
import Agda.Syntax.Common
import Agda.Syntax.Info
import Agda.TypeChecking.Monad
import qualified Agda.Syntax.Internal as I

checkFunDef :: DefInfo -> QName -> Delayed -> HasTypeSig -> [Clause] -> TCM ()
checkFunDef' :: I.Type -> Relevance -> Delayed -> DefInfo -> QName -> [Clause] -> TCM ()
