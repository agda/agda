module Agda.TypeChecking.Rules.Builtin.Coinduction where

import Agda.Syntax.Scope.Base
import Agda.TypeChecking.Monad

bindBuiltinInf   :: ResolvedName -> TCM ()
bindBuiltinSharp :: ResolvedName -> TCM ()
bindBuiltinFlat  :: ResolvedName -> TCM ()

