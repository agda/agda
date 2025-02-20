open import Agda.Builtin.Nat using () renaming (Nat to ℕ; zero to ze; suc to su)
open import Agda.Builtin.Equality using (_≡_; refl)

data Sort : Set where
  V   : Sort
  T>V : ∀ q → q ≡ V → Sort

pattern T = T>V V refl

variable
  q r s : Sort

_⊔_ : Sort → Sort → Sort
V ⊔ r = r
T ⊔ r = T

variable
  Γ Δ : ℕ

data Tm[_] : Sort → ℕ → Set where
  ƛ_  : Tm[ T ] (su Γ) → Tm[ T ] Γ

data Tms[_] (q : Sort) (Δ : ℕ) : ℕ → Set where
  _,_ : Tms[ q ] Δ Γ → Tm[ q ] Δ → Tms[ q ] Δ (su Γ)

postulate
  var0  : ∀ q → Tm[ q ] (su Γ)
  ε     : Tms[ q ] Δ ze

data Unit : Set where
  unit : Unit

mutual
  id : ∀ Γ → Tms[ V ] Γ Γ
  id (su Γ) = wks V Γ Γ (id Γ) , var0 V
  id ze     = ε

  wks : ∀ q Δ Γ → Tms[ q ] Δ Γ → Tms[ q ] (su Δ) Γ
  wks q Δ (su Γ) (δ , x) = wks q Δ Γ δ , wk q Δ x

  wk : ∀ q Γ → Tm[ q ] Γ → Tm[ q ] (su Γ)
  wk T Γ t = sub T V Γ (su Γ) t (wks V Γ Γ (id Γ))

  sub : ∀ q r Γ Δ →  Tm[ q ] Γ → Tms[ r ] Δ Γ → Tm[ q ⊔ r ] Δ
  sub q r Γ Δ (ƛ t) δ = ƛ (sub T r (su Γ) (su Δ) t (wks r Δ Γ δ , var0 r))

-- Used to be a termination error
-- *Arguably* should succeed
