module Agda.TypeChecking.Pretty.Warning where

import Agda.Utils.Pretty
import Agda.TypeChecking.Monad.Base
import {-# SOURCE #-} Agda.TypeChecking.Pretty (MonadPretty)

prettyWarning :: MonadPretty m => Warning -> m Doc
