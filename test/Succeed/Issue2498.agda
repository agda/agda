
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

record D (A : Set) : Set where
  constructor mkD
  field d : A
open D {{...}}

module test where

  instance

    _ : D Bool
    _ = mkD true

    a : D Nat
    a = mkD 0

  _ : d ≡ true
  _ = refl

  _ : d ≡ zero
  _ = refl

-- no instance in scope
-- _ : d ≡ true
-- _ = ?

_ : d ≡ zero
_ = refl
