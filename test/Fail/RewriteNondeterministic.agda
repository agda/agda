{-# OPTIONS --rewriting #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Equality

{-# BUILTIN REWRITE _≡_ #-}

postulate
  A : Set
  f : A → A
  a b c : A
  fa-to-b : f a ≡ b
  fx-to-c : ∀ x → f x ≡ c

{-# REWRITE fa-to-b #-}
{-# REWRITE fx-to-c #-}

test₁ : f a ≡ b
test₁ = refl

x : A

test₂ : f x ≡ c
test₂ = refl

x = a
