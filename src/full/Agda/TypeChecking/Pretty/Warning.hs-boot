{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.Pretty.Warning where

import Agda.TypeChecking.Monad.Base
import {-# SOURCE #-} Agda.TypeChecking.Pretty (MonadPretty)
import Agda.Syntax.Common.Pretty

prettyWarning :: MonadPretty m => Warning -> m Doc
