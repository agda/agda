{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.Empty
  ( isEmptyType
  , isEmptyTel
  , ensureEmptyType
  , checkEmptyTel
  ) where

import Agda.TypeChecking.Monad (TCM, MonadTCM)
import Agda.Syntax.Internal (Dom, Telescope, Type)
import Agda.Syntax.Position (Range)

data ErrorNonEmpty

isEmptyType :: MonadTCM tcm => Dom Type -> tcm Bool
isEmptyTel  :: MonadTCM tcm => Telescope -> tcm Bool

ensureEmptyType :: Range -> Dom Type -> TCM ()
checkEmptyTel   :: Range -> Telescope -> TCM (Either ErrorNonEmpty Int)
