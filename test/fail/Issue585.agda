-- {-# OPTIONS -v tc.conv:50 -v tc.reduce:100 -v tc:50 -v tc.term.expr.coind:15 -v tc.meta:20 #-}
-- 2012-03-15, reported by Nisse
module Issue585 where

open import Common.Coinduction

data ℕ : Set where
  zero : ℕ
  suc  : (n : ℕ) → ℕ

data Fin : ℕ → Set where
  zero : ∀ {n}         → Fin (suc n)
  suc  : ∀ {n} → Fin n → Fin (suc n)

data Vec (A : Set) : ℕ → Set where
  []  :                       Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

lookup : ∀ {n A} → Fin n → Vec A n → A
lookup zero    (x ∷ xs) = x
lookup (suc i) (x ∷ xs) = lookup i xs

infixl 9 _·_

data Tm (n : ℕ) : Set where
  var : Fin n → Tm n
  ƛ   : Tm (suc n) → Tm n
  _·_ : Tm n → Tm n → Tm n

infixr 8 _⇾_

data Ty : Set where
  _⇾_ : ∞ Ty → ∞ Ty → Ty

Ctxt : ℕ → Set
Ctxt n = Vec Ty n

infix 4 _⊢_∈_

data _⊢_∈_ {n} (Γ : Ctxt n) : Tm n → Ty → Set where
  var : ∀ {x} → Γ ⊢ var x ∈ lookup x Γ
  ƛ   : ∀ {t σ τ} → ♭ σ ∷ Γ ⊢ t ∈ ♭ τ → Γ ⊢ ƛ t ∈ σ ⇾ τ
  _·_ : ∀ {t₁ t₂ σ τ} → Γ ⊢ t₁ ∈ σ ⇾ τ → Γ ⊢ t₂ ∈ ♭ σ →
        Γ ⊢ t₁ · t₂ ∈ ♭ τ

Ω : Tm zero
Ω = ω · ω
  where ω = ƛ (var zero · var zero)

Ω-has-any-type : ∀ τ → [] ⊢ Ω ∈ τ
Ω-has-any-type τ =
  _·_ {σ = σ} {τ = ♯ _} (ƛ (var · var)) (ƛ (var · var))
  where
  σ : ∞ Ty
  σ = ♯ (σ ⇾ ♯ _) -- τ)

-- If the last
-- underscore is replaced by τ, then the code checks successfully.

-- WAS: Agda seems to loop when checking Ω-has-any-type.

-- NOW: this should leave metas unsolved.
