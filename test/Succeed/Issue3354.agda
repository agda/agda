
open import Agda.Builtin.Equality

postulate
  Ty Cxt : Set
  Var Tm : Ty → Cxt → Set
  _≤_ : (Γ Δ : Cxt) → Set

variable
  Γ Δ Φ : Cxt
  A B C : Ty
  x : Var A Γ

Mon : (P : Cxt → Set) → Set
Mon P = ∀{Δ Γ} (ρ : Δ ≤ Γ) → P Γ → P Δ

postulate
  _•_ : Mon (_≤ Φ)
  monVar : Mon (Var A)
  monTm : Mon (Tm A)

postulate
  refl-ish : {A : Set} {x y : A} → x ≡ y

variable
  ρ ρ' : Δ ≤ Γ

monVar-comp : monVar ρ (monVar ρ' x) ≡ monVar (ρ • ρ') x
monVar-comp {ρ = ρ} {ρ' = ρ'} {x = x} = refl-ish

variable
  t : Tm A Γ

monTm-comp : monTm ρ (monTm ρ' t) ≡ monTm (ρ • ρ') t
monTm-comp {ρ = ρ} {ρ' = ρ'} {t = t} = refl-ish
