open import Agda.Primitive

variable
  ℓ : Level
  A : Set ℓ

postulate
  w/e : ∀ {a} {A : Set a} → A

  Sub : {a : Level} (A : Set a) → (Set → A) → Set

  hcomp-equivFillerSub : Sub A (λ { _ → w/e {_} {_} })
