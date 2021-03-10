-- Andreas, 2018-09-08, issue #3211
--
-- Bug with parametrized module and constructor rewriting.

{-# OPTIONS --rewriting #-}
-- {-# OPTIONS -v rewriting.match:90 -v rewriting:90 #-}
-- {-# OPTIONS -v tc.getConType:50 #-}

module _ (Base : Set) where

open import Agda.Builtin.Equality
{-# BUILTIN REWRITE _≡_ #-}

cong : ∀ {a b} {A : Set a} {B : Set b}
       (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

data Form : Set where
  Atom : (P : Base) → Form
  _⇒_ : (A B : Form) → Form

data Cxt : Set where
  ε : Cxt
  _∙_ : (Γ : Cxt) (A : Form) → Cxt

infixl 4 _∙_
infix 3 _≤_

data _≤_ : (Γ Δ : Cxt) → Set where
  id≤ : ∀{Γ} → Γ ≤ Γ
  weak : ∀{A Γ Δ} (τ : Γ ≤ Δ) → Γ ∙ A ≤ Δ
  lift : ∀{A Γ Δ} (τ : Γ ≤ Δ) → Γ ∙ A ≤ Δ ∙ A

postulate lift-id≤ : ∀{Γ A} → lift id≤ ≡ id≤ {Γ ∙ A}
{-# REWRITE lift-id≤ #-}

Mon : (P : Cxt → Set) → Set
Mon P = ∀{Γ Δ} (τ : Γ ≤ Δ) → P Δ → P Γ

infix 2 _⊢_

data _⊢_ (Γ : Cxt) : (A : Form) → Set where
  impI   : ∀{A B} (t : Γ ∙ A ⊢ B) → Γ ⊢ A ⇒ B

Tm = λ A Γ → Γ ⊢ A

monD : ∀{A} → Mon (Tm A)
-- monD : ∀{A Γ Δ} (τ : Γ ≤ Δ) → Tm A Δ → Tm A Γ  -- Works
-- monD : ∀{A Γ Δ} (τ : Γ ≤ Δ) → Δ ⊢ A → Γ ⊢ A    -- Works
monD τ (impI t)    = impI (monD (lift τ) t)

monD-id : ∀{Γ A} (t : Γ ⊢ A) → monD id≤ t ≡ t
monD-id (impI t) = cong impI (monD-id t)  -- REWRITE lift-id≤

-- -}
