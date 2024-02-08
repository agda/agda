module Issue6972c where

open import Agda.Builtin.Equality

open import Issue6972b Set

opaque
  unfolding B

  _ : B ≡ Set
  _ = refl
