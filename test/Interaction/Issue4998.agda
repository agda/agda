
open import Agda.Builtin.Nat

record R : Set₁ where
  field f : Nat

open R ⦃ ... ⦄

foo : Nat → R
foo n .f = {!n!} -- C-c C-c makes clause disappear
