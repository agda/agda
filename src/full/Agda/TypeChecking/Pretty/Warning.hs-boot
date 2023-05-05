module Agda.TypeChecking.Pretty.Warning where

import Agda.Interaction.Options.Warnings (WarningName)
import Agda.TypeChecking.Monad.Base
import {-# SOURCE #-} Agda.TypeChecking.Pretty (MonadPretty)
import Agda.Utils.Pretty

prettyWarning :: MonadPretty m => Warning -> m Doc
prettyWarningName :: MonadPretty m => WarningName -> m Doc
