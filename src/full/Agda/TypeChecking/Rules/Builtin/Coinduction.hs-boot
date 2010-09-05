module Agda.TypeChecking.Rules.Builtin.Coinduction where

import Agda.Syntax.Abstract
import Agda.TypeChecking.Monad

bindBuiltinInf   :: Expr -> TCM ()
bindBuiltinSharp :: Expr -> TCM ()
bindBuiltinFlat  :: Expr -> TCM ()

data CoinductionKit = CoinductionKit
  { nameOfInf   :: QName
  , nameOfSharp :: QName
  , nameOfFlat  :: QName
  }

coinductionKit :: TCM (Maybe CoinductionKit)
