{-# OPTIONS --rewriting --confluence-check #-}

open import Common.Nat
open import Common.Equality

postulate _↦_ : ∀ {a} {A : Set a} → A → A → Set

{-# BUILTIN REWRITE _↦_ #-}

postulate
  P : ∀ {a} {A : Set a} → A → Set

postulate rew₁ : (f : Nat → Nat → Nat) → P (λ (x y z : Nat) → f z x) ↦ P f

{-# REWRITE rew₁ #-}

f : Nat → Nat → Nat → Nat
f x _ z = x + z

test : P f ≡ P (λ x z → z + x)
test = refl

postulate rew₂ : (f : Nat → Nat) → P (λ (x y : Nat) → f y) ↦ P f

{-# REWRITE rew₂ #-}

g : Nat → Nat → Nat
g x y = y

test₂ : P g ≡ P (λ (y : Nat) → y)
test₂ = refl

h : Nat → Nat → Nat → Nat
h x y z = x

test₃ : P h ≡ P (λ (z : Nat) → z)
test₃ = refl
