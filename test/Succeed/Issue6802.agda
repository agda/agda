module Issue6802 where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

-- Test case by Matthias Hutzler

opaque
  module _ where
    foo : Nat
    foo = zero

test : foo ≡ zero
test = refl  -- was error: foo != zero of type Nat
