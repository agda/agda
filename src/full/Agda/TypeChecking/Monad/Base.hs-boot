{-# LANGUAGE CPP #-}

module Agda.TypeChecking.Monad.Base where

import Control.Monad.IO.Class (MonadIO)
import Data.IORef (IORef)
import Data.Map (Map)

import Agda.Syntax.TopLevelModuleName (TopLevelModuleName)
import Agda.Utils.FileName (AbsolutePath)

data Definition
data Warning

data TCErr
data TCWarning
data NamedMeta
data HighlightingMethod
instance Show HighlightingMethod
instance Read HighlightingMethod

data HighlightingLevel
instance Show HighlightingLevel
instance Read HighlightingLevel


data TCEnv
data TCState
newtype TCMT m a = TCM { unTCM :: IORef TCState -> TCEnv -> m a }

instance Applicative m => Applicative (TCMT m)
instance Functor m => Functor (TCMT m)
instance MonadIO m => MonadIO (TCMT m)

#if __GLASGOW_HASKELL__ < 806
instance MonadIO m => Monad (TCMT m) where
#else
-- Andreas, 2022-02-02, issue #5659:
-- @transformers-0.6@ requires exactly a @Monad@ superclass constraint here
-- if we want @instance MonadTrans TCMT@.
instance Monad m => Monad (TCMT m) where
#endif

type TCM = TCMT IO

type ModuleToSource = Map TopLevelModuleName AbsolutePath

type BackendName = String

data Comparison
data IPFace' a
