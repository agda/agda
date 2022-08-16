
module Agda.TypeChecking.Pretty.Call where

import Agda.Syntax.Position

import Agda.TypeChecking.Monad.Base

import {-# SOURCE #-} Agda.TypeChecking.Pretty (MonadPretty, PrettyTCM)

import Agda.Utils.Pretty

sayWhen :: MonadPretty m => Range -> Maybe (Closure Call) -> m Doc -> m Doc
sayWhere :: MonadPretty m => HasRange a => a -> m Doc -> m Doc
instance PrettyTCM CallInfo
instance PrettyTCM Call
