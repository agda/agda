module OverlapLocal2 where

open import Agda.Builtin.Bool

postulate
  C : Bool → Set
  instance Ct : ∀ {x} → C x
  use : ∀ x → ⦃ _ : C x ⦄ → Set

-- The global instance is not overlappable, even if the local is more
-- specific.

_ : ⦃ local : C true ⦄ → Set
_ = use true
