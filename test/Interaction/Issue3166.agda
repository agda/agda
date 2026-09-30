
postulate Ty : Set

data Cxt : Set where
  ε : Cxt
  sg : (A : Ty) → Cxt
  _∙_ : (Γ₁ Γ₂ : Cxt) → Cxt

variable Γ Γ₁ Γ₂ Δ : Cxt

postulate Ren : (Δ Γ : Cxt) → Set

<_,_> : (f₁ : Ren Δ Γ₁) (f₂ : Ren Δ Γ₂) → Ren Δ (Γ₁ ∙ Γ₂)
<_,_> = {!!}

<_,_>₁ : (f₁ : Ren Δ Γ₁) (f₂ : Ren Δ Γ₂) → Cxt → Ren Δ (Γ₁ ∙ Γ₂)
< f₁ , f₂ >₁ x = {!!}
