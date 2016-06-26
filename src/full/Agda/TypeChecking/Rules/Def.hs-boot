module Agda.TypeChecking.Rules.Def where

import Agda.Syntax.Abstract as A
import Agda.Syntax.Common
import Agda.Syntax.Info
import Agda.TypeChecking.Monad
import qualified Agda.Syntax.Internal as I

checkFunDef :: Delayed -> DefInfo -> QName -> [Clause] -> TCM ()

checkFunDef' :: I.Type -> ArgInfo -> Delayed -> Maybe ExtLamInfo -> Maybe QName -> DefInfo -> QName -> [Clause] -> TCM ()

newSection :: ModuleName -> A.Telescope -> TCM a -> TCM a

useTerPragma :: Definition -> TCM Definition
