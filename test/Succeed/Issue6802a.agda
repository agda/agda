module Issue6802a where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

opaque
  record Foo : Set where
    foo : Nat
    foo = zero

test : Foo.foo _ ≡ zero
test = refl
