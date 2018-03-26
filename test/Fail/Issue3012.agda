
module _ where

record _×_ (A B : Set) : Set where
  field
    fst : A
    snd : B

open _×_

partial : ∀ {A B} → A → A × B
partial x .fst = x

open import Agda.Builtin.Equality

theorem : ∀ {A} (x : A) → partial x .snd ≡ x
theorem x = refl
