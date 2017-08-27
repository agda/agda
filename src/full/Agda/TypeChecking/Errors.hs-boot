module Agda.TypeChecking.Errors where

import Agda.TypeChecking.Monad.Base
import Agda.Syntax.Position

import Agda.Utils.Pretty

-- Misplaced SPECIALISE pragma:
-- {-# SPECIALIZE prettyError :: TCErr -> TCM String #-}
prettyError :: MonadTCM tcm => TCErr -> tcm String

prettyWarning :: MonadTCM tcm => Warning -> tcm Doc

sayWhen :: Range -> Maybe (Closure Call) -> TCM Doc -> TCM Doc
