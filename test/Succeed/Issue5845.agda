open import Agda.Builtin.Sigma

data Ctx : Set₁
Env : Ctx → Set

data Ctx where
  _∷_ : (Γ : Ctx) → (T : Env Γ → Set) → Ctx

Env (Γ ∷ T) = Σ (Env Γ) T

variable
  Γ : Ctx
  A T : Env _ → Set

data Tm : (Γ : Ctx) → (T : Env Γ → Set) → Set₁ where
  lam : Tm (Γ ∷ A) T
