module Agda.TypeChecking.Rules.Builtin.Coinduction where

import Agda.Syntax.Abstract
import Agda.TypeChecking.Monad

bindBuiltinInf   :: Expr -> TCM ()
bindBuiltinSharp :: Expr -> TCM ()
bindBuiltinFlat  :: Expr -> TCM ()

data CoinductionKit
inf   :: CoinductionKit -> QName
sharp :: CoinductionKit -> QName
flat  :: CoinductionKit -> QName

coinductionKit :: TCM (Maybe CoinductionKit)
