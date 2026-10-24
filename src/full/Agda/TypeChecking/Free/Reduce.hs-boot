{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.Free.Reduce where

import Agda.Syntax.Internal (Sort)
import Agda.TypeChecking.Free.Base (FlexRig)
import Agda.TypeChecking.Monad.Base (ReduceM)

data IsFree
  = MaybeFree !FlexRig
  | NotFree

forceNonDepSort :: Sort -> ReduceM (IsFree, Sort)
