module AnonymousRecConstrCopy2 where

module Foo (A : Set₁) where
  record Bar : Set where

module _ (let open Foo Set) where
  _ : Foo.Bar Set
  _ = Bar.constructor
