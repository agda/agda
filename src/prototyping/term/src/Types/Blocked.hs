{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

module Types.Blocked where

import Data.Foldable
import Data.Traversable

import IMPL.Term

data Blocked a = Blocked MetaVar a
               | NotBlocked a
  deriving (Functor, Foldable, Traversable)

ignoreBlocking :: Blocked a -> a
ignoreBlocking (NotBlocked x) = x
ignoreBlocking (Blocked _ x) = x
