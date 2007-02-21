{-# OPTIONS -fglasgow-exts #-}

module TypeChecking.Conversion where

import Control.Monad.Error
import Data.Generics
import Syntax.Internal
import TypeChecking.Monad

equalTerm :: (MonadError TCErr tcm, MonadTCM tcm) => Type -> Term -> Term -> tcm Constraints
equalType :: (MonadError TCErr tcm, MonadTCM tcm) => Type -> Type -> tcm Constraints
equalSort :: (MonadError TCErr tcm, MonadTCM tcm) => Sort -> Sort -> tcm Constraints
leqSort   :: (MonadError TCErr tcm, MonadTCM tcm) => Sort -> Sort -> tcm Constraints


