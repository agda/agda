-- Andreas, 2018-10-18, re issue #2757
--
-- Extracted this snippet from the standard library
-- as it caused problems during work in #2757
-- (runtime erasue using 0-quantity).

-- {-# OPTIONS -v tc.lhs.unify:65 -v tc.irr:50 #-}

{-# OPTIONS --sized-types #-}

open import Agda.Builtin.Size

data ⊥ : Set where

mutual
  data Conat (i : Size) : Set where
    zero : Conat i
    suc : ∞Conat i → Conat i

  record ∞Conat (i : Size) : Set where
    coinductive
    field force : ∀{j : Size< i} → Conat j
open ∞Conat

infinity : ∀ {i} → Conat i
infinity = suc λ where .force → infinity

data Finite : Conat ∞ → Set where
  zero : Finite zero
  suc  : ∀ {n} → Finite (n .force) → Finite (suc n)

¬Finite∞ : Finite infinity → ⊥
¬Finite∞ (suc p) = ¬Finite∞ p

-- The problem was that the usableMod check in the
-- unifier (LHS.Unify) refuted this pattern match
-- because a runtime-erased argument ∞ (via meta-variable)
-- the the extended lambda.
