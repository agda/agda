module AnonymousRecConstrRename where

-- Tests that Record.constructor syntax works even if the record has
-- been renamed.

module Foo where
  record Bar : Set₁ where
    field
      x : Set

open Foo renaming (Bar to Baz)

_ = Baz.constructor
