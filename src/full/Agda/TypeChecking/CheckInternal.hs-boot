{-# OPTIONS_GHC -Wunused-imports #-}

{-# LANGUAGE KindSignatures #-}

module Agda.TypeChecking.CheckInternal where

import qualified Data.Kind as Hs

import Agda.Syntax.Internal
import Agda.TypeChecking.Monad

data Action (m :: Hs.Type -> Hs.Type)

defaultAction :: PureTCM m => Action m
eraseUnusedAction :: Action TCM

class CheckInternal a where
  checkInternal' :: Action TCM -> a -> Comparison -> TypeOf a -> TCM a

  checkInternal :: a -> Comparison -> TypeOf a -> TCM ()
  checkInternal v cmp t = void $ checkInternal' defaultAction v cmp t

  inferInternal' :: (TypeOf a ~ ()) => Action TCM -> a -> TCM a
  inferInternal' act v = checkInternal' act v CmpEq ()

  inferInternal :: (TypeOf a ~ ()) => a -> TCM ()
  inferInternal v = checkInternal v CmpEq ()

instance CheckInternal Term
instance CheckInternal Type
instance CheckInternal Sort
instance CheckInternal Level
instance CheckInternal Elims

checkType :: Type -> TCM ()
infer :: Term -> TCM Type
