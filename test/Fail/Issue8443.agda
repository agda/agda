open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

module Issue8443 where

data ⊥ : Set where

module M1 (bot : ⊥) where
  foo : ⊥
  foo = bot

module M2 (n : Nat) where
  open M1 public

module M3           = M2
module M4           = M3 42

test : ⊥
test = M4.foo
