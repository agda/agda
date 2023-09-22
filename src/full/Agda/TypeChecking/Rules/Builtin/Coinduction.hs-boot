{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.Rules.Builtin.Coinduction where

import Agda.Syntax.Scope.Base
import Agda.Syntax.Internal (Type)
import Agda.TypeChecking.Monad

typeOfInf   :: TCM Type
typeOfSharp :: TCM Type
typeOfFlat  :: TCM Type

bindBuiltinInf   :: ResolvedName -> TCM ()
bindBuiltinSharp :: ResolvedName -> TCM ()
bindBuiltinFlat  :: ResolvedName -> TCM ()

