module OverlapLocal2 where

open import Agda.Builtin.Bool

postulate
  C : Bool → Set
  instance Ct : ∀ {x} → C x
  {-# OVERLAPPABLE Ct #-}
  use : ∀ x → ⦃ _ : C x ⦄ → Set

-- The local instance can overlap the global Ct

_ : ⦃ local : C true ⦄ → Set
_ = use true
