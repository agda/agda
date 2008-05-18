
module Logic.Structure.Applicative where

data Applicative (f : Set -> Set) : Set1 where
  applicative :
      (pure  : {a : Set} -> a -> f a)
      (_<*>_ : {a b : Set} -> f (a -> b) -> f a -> f b) ->
      Applicative f

module Applicative {f : Set -> Set}(App : Applicative f) where

  private
    pure' : Applicative f -> {a : Set} -> a -> f a
    pure' (applicative p _) = p

    app' : Applicative f -> {a b : Set} -> f (a -> b) -> f a -> f b
    app' (applicative _ a) = a

  pure : {a : Set} -> a -> f a
  pure = pure' App

  _<*>_ : {a b : Set} -> f (a -> b) -> f a -> f b
  _<*>_ = app' App

