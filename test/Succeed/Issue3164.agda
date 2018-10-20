
module _ where

open import Agda.Builtin.Equality

module _ (Ty : Set) where

  data Cxt : Set where
    sg : (A : Ty) → Cxt
    _∙_ : (Γ₁ Γ₂ : Cxt) → Cxt

  postulate Sub : Cxt → Cxt → Set

  variable Γ Δ : Cxt

  data Var (A : Ty) : Cxt → Set where
    •   : Var A (sg A)
    inl : (x : Var A Γ) → Var A (Γ ∙ Δ)

postulate
  T : ∀ {a} {A : Set a} → A → Set

  bla : T Γ

check-bla : {Ty : Set} {Γ : Cxt Ty} → T Γ
check-bla = bla
