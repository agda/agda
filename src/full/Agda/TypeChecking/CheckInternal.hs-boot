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

defaultAction :: PureTCM m => Action m
eraseUnusedAction :: Action TCM

class CheckInternal a where
  checkInternal' :: (MonadCheckInternal m) => Action m -> a -> Comparison -> TypeOf a -> m a

  checkInternal :: (MonadCheckInternal m) => a -> Comparison -> TypeOf a -> m ()
  checkInternal v cmp t = void $ checkInternal' defaultAction v cmp t

  inferInternal' :: (MonadCheckInternal m, TypeOf a ~ ()) => Action m -> a -> m a
  inferInternal' act v = checkInternal' act v CmpEq ()

  inferInternal :: (MonadCheckInternal m, TypeOf a ~ ()) => a -> m ()
  inferInternal v = checkInternal v CmpEq ()

instance CheckInternal Term
instance CheckInternal Type
instance CheckInternal Sort
instance CheckInternal Level
instance CheckInternal Elims

checkType :: (MonadCheckInternal m) => Type -> m ()
infer :: (MonadCheckInternal m) => Term -> m Type
