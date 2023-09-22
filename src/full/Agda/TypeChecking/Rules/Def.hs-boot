{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.Rules.Def where

import Agda.Syntax.Abstract as A
import Agda.Syntax.Common
import Agda.TypeChecking.Monad
import qualified Agda.Syntax.Internal as I

checkFunDef :: DefInfo -> QName -> [Clause] -> TCM ()

checkFunDef' :: I.Type -> ArgInfo -> Maybe ExtLamInfo -> Maybe QName -> DefInfo -> QName -> [Clause] -> TCM ()

newSection ::
   Erased -> ModuleName -> A.GeneralizeTelescope -> TCM a -> TCM a

useTerPragma :: Definition -> TCM Definition
