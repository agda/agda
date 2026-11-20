-- A variant of code reported by Andreas Abel, due to Andreas Abel and
-- Nicolas Pouillard.

-- npouillard, 2011-10-04

-- Andreas, 2026-10-12, issue #8829
-- Moved from test/Succeed/Issue1209-3.agda.
-- This proof of ⊥ is now rejected by the semi-continuity check:
-- the musical-coinductive Mu-co i is not lower semi-continuous in i,
-- so iter cannot recurse on i via the successor pattern.

{-# OPTIONS --guardedness --sized-types #-}

open import Common.Coinduction renaming (∞ to co)
open import Common.Size

data ⊥ : Set where

data Mu-co : Size → Set where
  inn : ∀ {i} → co (Mu-co i) → Mu-co (↑ i)

iter : ∀ {i} → Mu-co i → ⊥
iter (inn t) = iter (♭ t)

bla : Mu-co ∞
bla = inn (♯ bla)

false : ⊥
false = iter bla
