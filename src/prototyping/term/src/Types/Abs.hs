{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

module Types.Abs where

import Control.Applicative
import Data.Foldable
import Data.Traversable

data Abs a = Abs { absName :: String, absBody :: a }
  deriving (Show, Eq, Functor, Foldable, Traversable)

