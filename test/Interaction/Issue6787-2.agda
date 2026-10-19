{-# OPTIONS --safe --cubical-compatible #-}

open import Agda.Builtin.Equality

foo : ∀ {ℓ} {X : Set ℓ} {x : X} → _≡_ {A = x ≡ x} (refl {x = x}) (refl {x = x})
foo = {!!}
