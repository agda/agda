{-# LANGUAGE KindSignatures #-}

module Agda.TypeChecking.CheckInternal where

import qualified Control.Monad.Fail as Fail

import qualified Data.Kind as Hs

import Agda.Syntax.Internal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin (HasBuiltins)
import Agda.TypeChecking.Monad.Statistics (MonadStatistics)
import Agda.TypeChecking.Warnings
import Agda.Utils.Except ( MonadError )

type MonadCheckInternal m =
  ( MonadReduce m
  , MonadAddContext m
  , MonadConstraint m
  , MonadMetaSolver m
  , MonadError TCErr m
  , MonadWarning m
  , MonadDebug m
  , MonadStatistics m
  , MonadFresh ProblemId m
  , MonadFresh Int m
  , HasBuiltins m
  , HasConstInfo m
  , HasOptions m
  , Fail.MonadFail m
  )

data Action (m :: Hs.Type -> Hs.Type)

defaultAction :: Monad m => Action m
eraseUnusedAction :: Action TCM

checkType :: (MonadCheckInternal m) => Type -> m ()
checkType' :: (MonadCheckInternal m) => Type -> m Sort
checkSort :: (MonadCheckInternal m) => Action m -> Sort -> m Sort
checkInternal :: (MonadCheckInternal m) => Term -> Type -> m ()
checkInternal' :: (MonadCheckInternal m) => Action m -> Term -> Type -> m Term
infer :: (MonadCheckInternal m) => Term -> m Type
