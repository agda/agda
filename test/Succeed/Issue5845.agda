{-# OPTIONS --allow-unsolved-metas #-}

record ⊤ : Set where
record Σ-stx (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst

syntax Σ-stx A (λ x → B) = Σ[ x ∈ A ] B

module V (X : Set) (El : X → Set) where
  data V : Set where
    el : X → V
    Π : (i : X) → (El i → V) → V

  Sem : V → Set
  Sem (el S) = El S
  Sem (Π S T) = (s : El S) → Sem (T s)

  data Ctx : Set
  Env : Ctx → Set

  data Ctx where
    [] : Ctx
    _∷_ : (Γ : Ctx) → (T : Env Γ → X) → Ctx

  Env [] = ⊤
  Env (Γ ∷ T) = Σ[ γ ∈ Env Γ ] El (T γ)

  variable
    Γ : Ctx
    A B : Env Γ → X
    S T : Env Γ → V

module L (X : Set) (El : X → Set) where
  open V X El

  Π̂ : (A : Env Γ → X) (B : Env (Γ ∷ A) → V) → Env Γ → V
  Π̂ A B γ = Π (A γ) (λ a → B (γ , a))

  data Tm : (Γ : Ctx) → (T : Env Γ → V) → Set
  eval : Tm Γ T → (γ : Env Γ) → Sem (T γ)

  data Tm where
    lam : Tm (Γ ∷ A) T → Tm Γ (Π̂ A T)

  eval tm = {!!}
