{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.Errors where

import Agda.Syntax.Common (Cohesion, PolarityModality, Relevance, Hiding, Quantity)
import Agda.Syntax.Abstract.Name

import Agda.TypeChecking.Monad.Base
import {-# SOURCE #-} Agda.TypeChecking.Monad.Debug (MonadDebug)
import {-# SOURCE #-} Agda.TypeChecking.Pretty (PrettyTCM)

instance PrettyTCM TypeError
instance PrettyTCM TCErr

-- Misplaced SPECIALISE pragma:
-- {-# SPECIALIZE renderError :: TCErr -> TCM String #-}
renderError :: MonadTCM tcm => TCErr -> tcm String

topLevelModuleDropper :: (MonadDebug m, MonadTCEnv m, ReadTCState m) => m (QName -> QName)

class Verbalize a where
  verbalize :: a -> String

instance Verbalize Relevance
instance Verbalize Cohesion
instance Verbalize Hiding
instance Verbalize Quantity
instance Verbalize PolarityModality

newtype Indefinite a = Indefinite a
instance Verbalize a => Verbalize (Indefinite a)

newtype Ordinal = Ordinal Int
instance Verbalize Ordinal
