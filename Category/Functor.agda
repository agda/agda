------------------------------------------------------------------------
-- Functors
------------------------------------------------------------------------

-- Note that currently the functor laws are not included here.

module Category.Functor where

open import Data.Function

record RawFunctor (f : Set -> Set) : Set1 where
  field
    fmap : forall {a b} -> (a -> b) -> f a -> f b

module FunctorOps {f : Set -> Set} (fun : RawFunctor f) where

  private
    module RF = RawFunctor fun

  infixl 4 _<$>_ _<$_

  _<$>_ : forall {a b} -> (a -> b) -> f a -> f b
  _<$>_ = RF.fmap

  _<$_ : forall {a b} -> a -> f b -> f a
  x <$ y = const x <$> y
