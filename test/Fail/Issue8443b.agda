open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

module Issue8443b where

data ⊥ : Set where

module M1 (bot : ⊥) where
  module M2 (n : Nat) where
    foo : ⊥
    foo = bot

module M3 (n : Nat) where
  open M1 public

module M4 = M3
module M5 = M4 42

test : ⊥
test = M5.M2.foo 3
