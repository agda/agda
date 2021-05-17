open import Agda.Primitive

record R (a : Level) : Set (lsuc a) where
  field
    A : Set a

_ : ∀ a → R {!a!} → Set a
_ = λ _ → R.A
