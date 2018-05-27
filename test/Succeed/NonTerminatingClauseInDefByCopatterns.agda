{-# OPTIONS --copatterns #-}

open import Common.Prelude
open import Common.Product

postulate
  A : Set
  B : A → Set
  f : ∀ a → B a

bla : ∃ B
{-# NON_TERMINATING #-}
proj₁ bla = proj₁ bla
proj₂ bla = f (proj₁ bla)

T : Bool → Set
T true  = Bool
T false = Bool

test : (∀ b → T b) → ∃ T
{-# NON_TERMINATING #-}
proj₁ (test f) = proj₁ (test f)
proj₂ (test f) = f (proj₁ (test f))
