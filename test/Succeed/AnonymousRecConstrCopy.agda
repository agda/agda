module AnonymousRecConstrCopy where

module Foo (A : Set₁) where
  record Bar : Set where

open Foo Set

_ : Bar
_ = Bar.constructor
