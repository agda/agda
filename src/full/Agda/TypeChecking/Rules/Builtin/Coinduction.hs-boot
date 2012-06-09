module Agda.TypeChecking.Rules.Builtin.Coinduction where

import Agda.Syntax.Abstract
import Agda.TypeChecking.Monad

bindBuiltinInf   :: Expr -> TCM ()
bindBuiltinSharp :: Expr -> TCM ()
bindBuiltinFlat  :: Expr -> TCM ()

{- MOVED to TypeChecking.Monad.Builtin
data CoinductionKit
nameOfInf   :: CoinductionKit -> QName
nameOfSharp :: CoinductionKit -> QName
nameOfFlat  :: CoinductionKit -> QName

coinductionKit :: TCM (Maybe CoinductionKit)
-}
