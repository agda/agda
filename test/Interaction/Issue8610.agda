
module Issue8610 where

module Foo where
  data Nat : Set where
    z  : Nat
    s_ : Nat → Nat

open Foo
