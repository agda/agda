-- Andreas, 2018-05-11, issue #3051
-- Allow pattern synonyms in mutual blocks

open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality

id : ∀ {a} {A : Set a} → A → A
id x = x

_∘′_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
         (B → C) → (A → B) → (A → C)
f ∘′ g = λ x → f (g x)

_×̇_ : ∀{A C : Set} {B : A → Set} {D : C → Set}
     (f : A → C) (g : ∀{a} → B a → D (f a)) → Σ A B → Σ C D
(f ×̇ g) (x , y) = f x , g y

mutual
  data Cxt : Set₁ where
    _▷_ : (Γ : Cxt) (A : C⦅ Γ ⦆ → Set) → Cxt

  C⦅_⦆ : Cxt → Set
  C⦅ Γ ▷ A ⦆ = Σ C⦅ Γ ⦆ A

mutual
  data _≤_ : (Δ Γ : Cxt) → Set₁ where
    id≤  : ∀{Γ} → Γ ≤ Γ
    weak : ∀{Γ Δ A} (τ : Δ ≤ Γ) → (Δ ▷ A) ≤ Γ
    lift' : ∀{Γ Δ A A'} (τ : Δ ≤ Γ) (p : A' ≡ (A ∘′ τ⦅ τ ⦆)) → (Δ ▷ A') ≤ (Γ ▷ A)

  pattern lift τ = lift' τ refl

  τ⦅_⦆ : ∀{Γ Δ} (τ : Δ ≤ Γ) → C⦅ Δ ⦆ → C⦅ Γ ⦆
  τ⦅ id≤ ⦆ = id
  τ⦅ weak τ ⦆ = τ⦅ τ ⦆ ∘′ fst
  τ⦅ lift τ ⦆ = τ⦅ τ ⦆ ×̇ id

-- Should pass.
