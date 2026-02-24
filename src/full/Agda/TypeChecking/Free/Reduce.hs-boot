{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.Free.Reduce where

import Agda.Syntax.Internal (Abs, Sort, Type, Dom)
import Agda.TypeChecking.Free.Base (FlexRig)
import Agda.TypeChecking.Monad.Base (ReduceM)

forceNoAbsSort :: Dom Type -> Abs Sort -> ReduceM (Either (Abs Sort, FlexRig) Sort)
