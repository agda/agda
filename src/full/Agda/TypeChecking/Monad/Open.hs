-- {-# LANGUAGE CPP #-}

module Agda.TypeChecking.Monad.Open
        ( makeOpen
        , getOpen
        ) where

import Control.Monad
import Control.Monad.Reader
import qualified Data.List as List

import Agda.Syntax.Internal
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Monad.Base

import {-# SOURCE #-} Agda.TypeChecking.Monad.Context

import Agda.Utils.Lens
import Agda.Utils.Except ( MonadError(catchError) )

-- | Create an open term in the current context.
makeOpen :: a -> TCM (Open a)
makeOpen x = do
    cp <- view eCurrentCheckpoint
    return $ OpenThing cp x

-- | Extract the value from an open term. The checkpoint at which it was
--   created must be in scope.
getOpen :: (Subst Term a, MonadReader TCEnv m) => Open a -> m a
getOpen (OpenThing cp x) = do
  sub <- checkpointSubstitution cp
  return $ applySubst sub x

