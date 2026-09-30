-- Andreas, 2016-07-13, issue reported by Mietek Bak

-- {-# OPTIONS -v tc.size:20  #-}
-- {-# OPTIONS -v tc.meta.assign:30 #-}

{-# OPTIONS --sized-types #-}

open import Agda.Builtin.Size

data Cx (U : Set) : Set where
  ⌀   : Cx U
  _,_ : Cx U → U → Cx U

data _∈_ {U : Set} (A : U) : Cx U → Set where
  top : ∀ {Γ} → A ∈ (Γ , A)
  pop : ∀ {C Γ} → A ∈ Γ → A ∈ (Γ , C)

infixr 3 _⊃_
data Ty : Set where
  ι   : Ty
  _⊃_ : Ty → Ty → Ty

infix 1 _⊢⟨_⟩_
data _⊢⟨_⟩_ (Γ : Cx Ty) : Size → Ty → Set where
  var : ∀ {m A}                     → A ∈ Γ → Γ ⊢⟨ m ⟩ A
  lam : ∀ {m A B} {m′ : Size< m}    → Γ , A ⊢⟨ m′ ⟩ B → Γ ⊢⟨ m ⟩ A ⊃ B
  app : ∀ {m A B} {m′ m″ : Size< m} → Γ ⊢⟨ m′ ⟩ A ⊃ B → Γ ⊢⟨ m″ ⟩ A → Γ ⊢⟨ m ⟩ B

works : ∀ {m A B Γ} → Γ ⊢⟨ ↑ ↑ ↑ ↑ m ⟩ (A ⊃ A ⊃ B) ⊃ A ⊃ B
works = lam (lam (app (app (var (pop top)) (var top)) (var top)))

test : ∀ {m A B Γ} → Γ ⊢⟨ {!↑ ↑ ↑ ↑ m!} ⟩ (A ⊃ A ⊃ B) ⊃ A ⊃ B
test = lam (lam (app (app (var (pop top)) (var top)) (var top)))

-- This interaction meta should be solvable with
--   ↑ ↑ ↑ ↑ m
-- Give should succeed.
-- The problem was: premature instantiation to ∞.
