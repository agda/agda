{-# LANGUAGE KindSignatures #-}

module Agda.TypeChecking.CheckInternal where

import Control.Monad.Except
import qualified Control.Monad.Fail as Fail

import qualified Data.Kind as Hs

import Agda.Syntax.Internal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Warnings

type MonadCheckInternal m =
  ( PureTCM m
  , MonadConstraint m
  , MonadMetaSolver m
  , MonadError TCErr m
  , MonadWarning m
  , MonadStatistics m
  , MonadFresh ProblemId m
  , MonadFresh Int m
  , Fail.MonadFail m
  )

data Action (m :: Hs.Type -> Hs.Type)

defaultAction :: Monad m => Action m
eraseUnusedAction :: Action TCM

checkType :: (MonadCheckInternal m) => Type -> m ()
checkType' :: (MonadCheckInternal m) => Type -> m Sort
checkSort :: (MonadCheckInternal m) => Action m -> Sort -> m Sort
checkInternal :: (MonadCheckInternal m) => Term -> Comparison -> Type -> m ()
checkInternal' :: (MonadCheckInternal m) => Action m -> Term -> Comparison -> Type -> m Term
infer :: (MonadCheckInternal m) => Term -> m Type
