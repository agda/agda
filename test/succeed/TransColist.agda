-- Andreas, 2011-09-13, shrunk from Data.Colist
-- {-# OPTIONS -v tc.lhs.unify:15 #-}

{-# OPTIONS --universe-polymorphism #-}

module TransColist where

open import Common.Level
open import Common.Coinduction

-- From Relation.Binary.Core:
------------------------------------------------------------------------
-- Binary relations

-- Heterogeneous binary relations

REL : ∀ {a b} → Set a → Set b → (ℓ : Level) → Set (a ⊔ b ⊔ lsuc ℓ)
REL A B ℓ = A → B → Set ℓ

-- Homogeneous binary relations

Rel : ∀ {a} → Set a → (ℓ : Level) → Set (a ⊔ lsuc ℓ)
Rel A ℓ = REL A A ℓ

-- Generalised transitivity.

Trans : ∀ {a b c ℓ₁ ℓ₂ ℓ₃} {A : Set a} {B : Set b} {C : Set c} →
        REL A B ℓ₁ → REL B C ℓ₂ → REL A C ℓ₃ → Set _
Trans P Q R = ∀ {i j k} → P i j → Q j k → R i k

Transitive : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Set _
Transitive _∼_ = Trans _∼_ _∼_ _∼_

infixr 5 _∷_

data Colist {a} (A : Set a) : Set a where
  []  : Colist A
  _∷_ : (x : A) (xs : ∞ (Colist A)) → Colist A

infix 4 _≈_

data _≈_ {a} {A : Set a} : (xs ys : Colist A) → Set a where
  []  :                                       []     ≈ []
  _∷_ : ∀ x {xs ys} (xs≈ : ∞ (♭ xs ≈ ♭ ys)) → x ∷ xs ≈ x ∷ ys

postulate
  a : Level
  A : Set a
{- succeeds:
trans : -- forall {a}{A : Set a}
        forall {xs ys zs : Colist A} → 
  xs ≈ ys → ys ≈ zs →  xs ≈ zs
-}

-- succeeds:
-- trans : forall {a}{A : Set a}{xs ys zs : Colist A} → xs ≈ ys → ys ≈ zs →  xs ≈ zs

trans : Transitive (_≈_ {A = A})
trans []        []         = []
trans (x ∷ xs≈) (.x ∷ ys≈) = x ∷ ♯ trans (♭ xs≈) (♭ ys≈)


