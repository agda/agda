-- Andreas, 2024-08-20, issue #7439, trigger SafeFlagNoUniverseCheck

{-# OPTIONS --safe #-}

module _ where

data ⊥ : Set where

{-# NO_UNIVERSE_CHECK #-}  -- rejected with --safe
record Type : Set where
  constructor inn
  field out : Set
open Type

-- The rest is Hurken's paradox.

⊥′ : Type
⊥′ = inn ((A : Type) → out A)

_⇒_ : (A B : Type) → Type
inn A ⇒ inn B = inn (A → B)

Π : (A : Type) (B : out A → Type) → Type
Π A B = inn ((x : out A) → out (B x))

¬_ : Type → Type
¬ A = A ⇒ ⊥′

P : Type → Type
P A = inn (out A → Type)

U : Type
U = inn ((X : Type) → out ((P (P X) ⇒ X) ⇒ P (P X)))

τ : out (P (P U) ⇒ U)
τ t = λ X f p → t λ x → p (f (x X f))

σ : out (U ⇒ P (P U))
σ s pu = s U (λ t → τ t) pu

Δ : out (P U)
Δ = λ y → ¬ (Π (P U) λ p → σ y p ⇒ p (τ (σ y)))

Ω : out U
Ω X t px = τ (λ p → Π U λ x → σ x p ⇒ p x) X t px

D : Type
D = Π (P U) λ p → σ Ω p ⇒ p (τ (σ Ω))

lem₁ : out (Π (P U) λ p → (Π U λ x → σ x p ⇒ p x) ⇒ p Ω)
lem₁ p H1 = H1 Ω λ x → H1 (τ (σ x))

lem₂ : out (¬ D)
lem₂ d A = lem₁ Δ (λ x H2 H3 → H3 Δ H2 λ p → H3 λ y → p (τ (σ y))) d A

lem₃ : out D
lem₃ p = lem₁ λ y → p (τ (σ y))

loop : out ⊥′
loop = λ A → lem₂ lem₃ A

absurd : ⊥
absurd = loop (inn ⊥)
