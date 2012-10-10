
module Subst where

import Level

postulate Ty : Set

data Cxt : Set where
  ε   : Cxt
  _,_ : (Γ : Cxt) (A : Ty) → Cxt

_++_ : Cxt → Cxt → Cxt
Γ ++ ε       = Γ
Γ ++ (Δ , A) = (Γ ++ Δ) , A

data Tm : Cxt → Ty → Set where
  vz : ∀ {Γ A} → Tm (Γ , A) A
  other : ∀ {Γ A} → Tm Γ A

data _≡_ {a}{A : Set a}(x : A) : A → Set a where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

data Sub : Cxt → Cxt → Set where
  _∷_  : ∀ {Γ Δ A} → Tm Γ A → Sub Γ Δ → Sub Γ (Δ , A)
  lift : ∀ {Γ Δ} Ψ → Sub Γ Δ → Sub (Γ ++ Ψ) (Δ ++ Ψ)
  wk   : ∀ {Γ Δ} Ψ → Sub Γ Δ → Sub (Γ ++ Ψ) Δ
  id   : ∀ {Γ} → Sub Γ Γ
  ∅    : ∀ {Γ} → Sub Γ ε

assoc : ∀ {Γ Δ} Ψ → (Γ ++ (Δ ++ Ψ)) ≡ ((Γ ++ Δ) ++ Ψ)
assoc ε = refl
assoc {Γ}{Δ} (Ψ , A) rewrite assoc {Γ} {Δ} Ψ = refl

ε++ : ∀ Γ → (ε ++ Γ) ≡ Γ
ε++ ε = refl
ε++ (Γ , A) rewrite ε++ Γ = refl

postulate

  apply : ∀ {Γ Δ A} → Sub Γ Δ → Tm Δ A → Tm Γ A

sym : ∀ {A : Set}{x y : A} → x ≡ y → y ≡ x
sym refl = refl

cast : ∀ {Γ₁ Γ₂ Δ₁ Δ₂} → Γ₁ ≡ Γ₂ → Δ₁ ≡ Δ₂ → Sub Γ₁ Δ₁ → Sub Γ₂ Δ₂
cast refl refl ρ = ρ

inj : ∀ {Γ Δ A B} → (Γ , A) ≡ (Δ , B) → Γ ≡ Δ
inj refl = refl

injT : ∀ {Γ Δ A B} → (Γ , A) ≡ (Δ , B) → A ≡ B
injT refl = refl

drop : ∀ {Γ Δ ΔΨ} Ψ → Sub Γ ΔΨ → ΔΨ ≡ (Δ ++ Ψ) → Sub Γ Δ
drop Ψ id refl = wk Ψ id
drop Ψ (wk Δ ρ) refl = wk Δ (drop Ψ ρ refl)
drop Ψ (lift ε ρ) refl = drop Ψ ρ refl
drop ε ρ refl = ρ
drop (Ψ , A) (x ∷ ρ) refl = drop Ψ ρ refl
drop {Δ = Δ} (Ψ , A) (lift {Γ = Γ}{Δ = Σ} (Θ , A′) ρ) eq =
     wk (ε , A′) (drop Ψ (lift Θ ρ) (inj eq))
drop (Ψ , A) ∅ ()

wkS : ∀ {Γ Δ} Ψ → Sub Γ Δ → Sub (Γ ++ Ψ) Δ
wkS ε ρ = ρ
wkS Ψ (x ∷ ρ) = (apply (wk Ψ id) x) ∷ wkS Ψ ρ
wkS Ψ (lift Ψ₁ ρ) = wk Ψ (lift Ψ₁ ρ)
wkS Ψ (wk Ψ₁ ρ) = cast (assoc Ψ) refl (wkS (Ψ₁ ++ Ψ) ρ) 
wkS Ψ id = wk Ψ id
wkS Ψ ∅ = ∅

liftS : ∀ {Γ Δ} Ψ → Sub Γ Δ → Sub (Γ ++ Ψ) (Δ ++ Ψ)
liftS Ψ (x ∷ ρ) = lift Ψ (x ∷ ρ)
liftS Ψ (lift Ψ₁ ρ) = cast (assoc Ψ) (assoc Ψ) (liftS (Ψ₁ ++ Ψ) ρ)
liftS Ψ (wk Ψ₁ ρ) = lift Ψ (wk Ψ₁ ρ)
liftS Ψ id = id
liftS Ψ ∅ = lift Ψ ∅

data _×_ A B : Set where
  _,_ : A → B → A × B

split : ∀ {Γ Δ ΔΨ} Ψ → Sub Γ ΔΨ → ΔΨ ≡ (Δ ++ Ψ) → Sub Γ Δ × Sub Γ Ψ
split {Γ} ε ρ refl = ρ , ∅
split (Ψ , A) (x ∷ ρ) refl with split Ψ ρ refl
... | σ , δ = σ , (x ∷ δ)
split Ψ (lift ε ρ) eq = split Ψ ρ eq
split (Ψ , A) (lift (Ψ₁ , A₁) ρ) eq with split Ψ (lift Ψ₁ ρ) (inj eq) | injT eq
split (Ψ , A) (lift (Ψ₁ , .A) ρ) eq | σ , δ | refl =
  wk (ε , A) σ , lift (ε , A) δ
split Ψ (wk Ψ₁ ρ) eq with split Ψ ρ eq
... | σ , δ = wk Ψ₁ σ , wk Ψ₁ δ
split {Δ = Δ} Ψ id refl = wk Ψ id , cast refl (ε++ Ψ) (lift {Γ = Δ} Ψ ∅)
split (Ψ , A) ∅ ()

_<>_ : ∀ {Γ Δ Ψ} → Sub Γ Ψ → Sub Γ Δ → Sub Γ (Δ ++ Ψ)
(x ∷ ρ) <> σ = x ∷ (ρ <> σ)
lift Ψ ρ <> σ = {!!}
wk Ψ₁ ρ <> σ = {!!}
-- _<>_ {Ψ = Ψ} id (_∷_ {Δ = Δ}{A = A} x σ) = cast refl (assoc {_}{ε , A} Ψ)
--   (_<>_ {Ψ = (ε , A) ++ Ψ} {!!} σ)
id <> lift Ψ σ = {!!}
id <> wk Ψ σ = {!!}
id <> id = {!!}
_<>_ {Ψ = Ψ} id ∅ = cast (ε++ Ψ) refl id
_<>_ {Ψ = ε} id σ = {!!}
_<>_ {Ψ = Ψ , A} id σ = vz ∷ (_<>_ {Ψ = Ψ} (wk (ε , A) id) σ)
∅ <> σ = σ

comp : ∀ {Γ Δ Δ′ Ψ} → Sub Γ Δ → Sub Δ′ Ψ → Δ ≡ Δ′ → Sub Γ Ψ
comp ρ id refl = ρ
comp ρ (wk Δ σ) refl = comp (drop Δ ρ refl) σ refl
comp ρ (x ∷ σ) refl = apply ρ x ∷ comp ρ σ refl
comp ρ (lift ε σ) refl = comp ρ σ refl
comp ρ (lift Ψ σ) refl with split Ψ ρ refl
... | ρ₁ , ρ₂ = ρ₂ <> comp ρ₁ σ refl
comp {Γ} ∅ σ refl = cast (ε++ Γ) refl (wk Γ σ)
-- comp (u ∷ ρ) (lift (Ψ , A) σ) eq
--   with injT eq
-- ... | refl = u ∷ comp ρ (lift Ψ σ) (inj eq)
-- comp ρ (lift (Ψ , A) σ) eq =
--   apply (cast refl eq ρ) vz ∷
--   comp ρ (wk (ε , A) (lift Ψ σ)) eq
comp ρ ∅ refl = ∅

_∘_ : ∀ {Γ Δ Ψ} → Sub Γ Δ → Sub Δ Ψ → Sub Γ Ψ
ρ ∘ σ = comp ρ σ refl
