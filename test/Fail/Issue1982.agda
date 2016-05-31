open import Agda.Builtin.Nat

data Tm : Nat → Set where
  UP : ∀ {n} → Tm n → Tm n

!_ : ∀ {n} → Tm n → Tm (suc n)
! UP t = UP (! t)

data Ty : Nat → Set where
  ⊥ : ∀ {n} → Ty n
  _∶_ : ∀ {n} → Tm n → Ty n → Ty (suc n)

data Cx : Set where
  ∅ : Cx
  _,_ : ∀ {n} → Cx → Ty n → Cx

data _⊇_ : Cx → Cx → Set where
  base : ∅ ⊇ ∅
  weak : ∀ {Γ Γ′ n} {A : Ty n} → Γ′ ⊇ Γ → (Γ′ , A) ⊇ Γ
  lift : ∀ {Γ Γ′ n} {A : Ty n} → Γ′ ⊇ Γ → (Γ′ , A) ⊇ (Γ , A)

data True (Γ : Cx) : ∀ {n} → Ty n → Set where
  up : ∀ {n} {t : Tm n} {A : Ty n} → True Γ (t ∶ A) → True Γ ((! t) ∶ (t ∶ A))

ren-true--pass : ∀ {n Γ Γ′} {A : Ty n} → Γ′ ⊇ Γ → True Γ A → True Γ′ A
ren-true--pass η (up j) = up (ren-true--pass η j)

ren-true--fail : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → True Γ A → True Γ′ A
ren-true--fail η (up j) = up (ren-true--fail η j)
