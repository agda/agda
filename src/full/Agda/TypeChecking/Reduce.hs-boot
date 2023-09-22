{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.Reduce where

import Agda.Syntax.Internal (Term, Elims, QName)
import Agda.TypeChecking.Monad.Base (TCM, Reduced)

reduceDefCopyTCM :: QName -> Elims -> TCM (Reduced () Term)
