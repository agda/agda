{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.Pretty.Call where

import Agda.TypeChecking.Monad.Base
import {-# SOURCE #-} Agda.TypeChecking.Pretty (PrettyTCM)

instance PrettyTCM Call
