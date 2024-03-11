module OverlapLocal1 where

open import Agda.Builtin.Bool

postulate
  C : Bool → Set
  instance Ct : C true
  {-# OVERLAPPABLE Ct #-}
  use : ∀ x → ⦃ _ : C x ⦄ → Set

-- The global instance *could* be overlapped, including by a local, but
-- 'local' is not more specific than it.

_ : ⦃ local : ∀ {x} → C x ⦄ → Set
_ = use true
