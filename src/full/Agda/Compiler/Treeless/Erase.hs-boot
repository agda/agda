{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.Compiler.Treeless.Erase where

import Agda.TypeChecking.Monad.Base (TCM)
import Agda.Syntax.Abstract.Name (QName)

isErasable :: QName -> TCM Bool
