module OverlapLocal1 where

open import Agda.Builtin.Bool

postulate
  C : Bool → Set
  instance Ct : C true
  {-# OVERLAPPING Ct #-}
  use : ∀ x → ⦃ _ : C x ⦄ → Set

-- The global Ct can overlap the local instance

_ : ⦃ local : ∀ {x} → C x ⦄ → Set
_ = use true
