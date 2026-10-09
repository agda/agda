{-# OPTIONS --safe --without-K #-}

{- Issue #8704, variant without abstract or opaque.

Clause-based reduction used to skip a clause if matching got stuck only on
lazy (forced) patterns while all non-lazy patterns matched (#7181).
This assumes that the lazy patterns must then match as well, which is false
if the term matches the lazy pattern only up to eta.

-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality

------------------------------------------------------------------------
-- Preliminaries

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

data ⊥ : Set where

false≢true : false ≡ true → ⊥
false≢true ()

------------------------------------------------------------------------
-- Actual exploit

ℕ×ℕ : Set
ℕ×ℕ = Σ Nat λ _ → Nat

data D : ℕ×ℕ → Set where
  mk    : (a b : Nat) → D (a , b)
  other : (p : ℕ×ℕ) → D p         -- This is to allow clauses 2 and 3 in g

mk' : (p : ℕ×ℕ) → D p
mk' p = mk (fst p) (snd p)

g : (p : ℕ×ℕ) → D p → Bool → Bool

-- The first argument becomes a lazy (forced) pattern (a , b).
g .(a , b) (mk a b) _ = true

-- We need the first two clauses in scope but not yet translated to case-trees.
-- So we have a third clause with a local module that is checked
-- using clause-based reduction for the first two-clauses.
{-# CATCHALL #-}
g p d true  = false
g p d false = false
  module ClauseBasedReduction where
    -- The lazy pattern (a , b) is stuck on the variable p,
    -- while the non-lazy pattern mk matches.
    -- Skipping to the next clause would make this hold by refl.
    lemma : g p (mk' p) true ≡ false
    lemma = refl

-- The case tree does not split on the lazy pattern, so the first clause fires.
lemma' : (p : ℕ×ℕ) → g p (mk' p) true ≡ true
lemma' p = refl

false≡true : false ≡ true
false≡true = trans
  (sym (ClauseBasedReduction.lemma (0 , 0) (mk 0 0)))
  (lemma' (0 , 0))

absurd : ⊥
absurd = false≢true false≡true
