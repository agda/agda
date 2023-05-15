module InjectiveForInferencePragma where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma

_×_ : Set → Set → Set
A × B = Σ A (λ _ → B)

f : {A : Set} → Nat × A → Nat × A
f (n , a) = (0 , a)

{-# INJECTIVE_FOR_INFERENCE f #-}

snd-f-cong : ∀ {A} {a a' : Nat × A} → snd a ≡ snd a' → f a ≡ f a'
snd-f-cong refl = refl

f-≡ : ∀ {A} {a : A} → f (0 , a) ≡ f (1 , a)
f-≡ = snd-f-cong refl
