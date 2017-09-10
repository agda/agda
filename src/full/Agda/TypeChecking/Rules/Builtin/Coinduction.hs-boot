module Agda.TypeChecking.Rules.Builtin.Coinduction where

import Agda.Syntax.Abstract
import Agda.Syntax.Scope.Base
import Agda.TypeChecking.Monad

bindBuiltinInf   :: ResolvedName -> TCM ()
bindBuiltinSharp :: ResolvedName -> TCM ()
bindBuiltinFlat  :: ResolvedName -> TCM ()

{- MOVED to TypeChecking.Monad.Builtin
data CoinductionKit
nameOfInf   :: CoinductionKit -> QName
nameOfSharp :: CoinductionKit -> QName
nameOfFlat  :: CoinductionKit -> QName

coinductionKit :: TCM (Maybe CoinductionKit)
-}
