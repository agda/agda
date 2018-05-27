-- Andreas and James, 2013-11-19

{-# OPTIONS --copatterns  #-}
-- {-# OPTIONS -v tc.cover.splittree:15 -v tc.cc:15 #-}

open import Common.Level
open import Common.Product

mutual
  data Delay (A : Set) : Set where
    later : ∞Delay A → Delay A

  record ∞Delay (A : Set) : Set where
    coinductive
    constructor delay
    field
      force : Delay A
open ∞Delay public

data Def {A : Set} : Delay A → Set where
  later⇓ : ∀ (x : ∞Delay A) → Def (force x) → Def (later x)

data Ty : Set where
  _⇒_ : (a b : Ty) → Ty

data Tm (Γ : Ty) : (a : Ty) → Set where
  abs : ∀ a b (t : Tm (Γ ⇒ a) b) → Tm Γ (a ⇒ b)

data Val : (a : Ty) → Set where
  lam : ∀ Γ a b (t : Tm (Γ ⇒ a) b) → Val (a ⇒ b)

postulate
  eval : ∀ Γ a → Tm Γ a → Delay (Val a)

∞apply : ∀ a b → Val (a ⇒ b) → ∞Delay (Val b)
force (∞apply .a .b (lam Γ a b t)) = eval (Γ ⇒ a) b t

β-expand : ∀ Γ a b (t : Tm (Γ ⇒ a) b) →
  Def (eval (Γ ⇒ a) b t) → Def (later (∞apply a b (lam Γ a b t)))
β-expand Γ a b t = later⇓ (∞apply a b (lam Γ a b t))

-- This line failed because of a missing reduction (due to wrong split tree).
