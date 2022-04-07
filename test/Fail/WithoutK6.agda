{-# OPTIONS --cubical-compatible --show-implicit #-}

module WithoutK6 where

-- Equality defined with two indices.

data _≡_ {A : Set} : A → A → Set where
  refl : ∀ x → x ≡ x

weak-K : {A : Set} {a b : A} (p q : a ≡ b) (α β : p ≡ q) → α ≡ β
weak-K (refl a) .(refl a) (refl .(refl a)) (refl .(refl a)) =
  refl (refl (refl a))
