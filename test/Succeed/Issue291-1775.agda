-- Andreas, 2011-04-14
-- {-# OPTIONS -v tc.cover:20 -v tc.lhs.unify:20 #-}

-- Jesper, 2016-06-23: should also work --cubical-compatible
{-# OPTIONS --cubical-compatible #-}

module Issue291-1775 where

-- Example by Ulf

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

data _≡_ {A : Set}(a : A) : A -> Set where
  refl : a ≡ a

-- since 'n' occurs stronly rigid in 'suc n', the type 'n ≡ suc n' is empty
h : (n : Nat) -> n ≡ suc n -> Nat
h n ()

-- Example by jdanbr...@gmail.com

data Type : Set where
  ₁   : Type
  _×_ : Type → Type → Type
  _+_ : Type → Type → Type

data Fun : Type → Type → Set where
  _∙_ : ∀ {s t u} → Fun t u → Fun s t → Fun s u
  π₁  : ∀ {s t} →   Fun (s × t) s
  π₂  : ∀ {s t} →   Fun (s × t) t
  ι₁  : ∀ {s t} →   Fun s (s + t)
  ι₂  : ∀ {s t} →   Fun t (s + t)

data Val : (t : Type) → Fun ₁ t → Set where
  Valι₁ : ∀ {s t V} → Val s V → Val (s + t) (ι₁ ∙ V)
  Valι₂ : ∀ {s t V} → Val t V → Val (s + t) (ι₂ ∙ V)

data ⊥ : Set where

-- should succeed:
¬Valπ₁ : ∀ {s t : Type} {M : Fun ₁ (s × t)} → Val s (π₁ ∙ M) → ⊥
¬Valπ₁ ()
{- OLD ERROR:
Val .s (π₁ ∙ .M) should be empty, but it isn't obvious that it is.
when checking that the clause ¬Valπ₁ () has type
{s t : Type} {M : Fun ₁ (s × t)} → Val s (π₁ ∙ M) → ⊥
-}
