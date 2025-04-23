{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.Empty
  ( isEmptyType
  , isEmptyTel
  , ensureEmptyType
  , checkEmptyTel
  ) where

import Agda.TypeChecking.Monad (TCM, MonadTCM)
import Agda.Syntax.Internal (Type, Telescope)
import Agda.Syntax.Position (Range)

data ErrorNonEmpty

isEmptyType :: MonadTCM tcm => Type -> tcm Bool
isEmptyTel  :: MonadTCM tcm => Telescope -> tcm Bool

ensureEmptyType :: Range -> Type -> TCM ()
checkEmptyTel   :: Range -> Telescope -> TCM (Either ErrorNonEmpty Int)
