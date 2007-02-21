{-# OPTIONS -fglasgow-exts #-}

module TypeChecking.MetaVars where

import Control.Monad.Error     ( MonadError )
import Syntax.Internal	       ( MetaId, Term )
import TypeChecking.Monad.Base ( TCErr, MonadTCM )

assignTerm :: (MonadError TCErr tcm, MonadTCM tcm) => MetaId -> Term -> tcm ()

