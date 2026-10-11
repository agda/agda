-- Andreas, 2026-10-08
-- Mimer should accept a candidate whose type only unifies with the goal
-- after the candidate's subgoals have been solved.
-- Here, f ?n = f n is blocked on the subgoal ?n.

module Issue8815 where

open import Agda.Builtin.Nat renaming (Nat to N; zero to z; suc to s)

f : N → N
f z     = z
f (s n) = n

postulate
  P     : N → Set
  lemma : {n : N} → P n → P (f n)

test₁ : {n : N} → P n → P (f n)
test₁ p = {! lemma !}  -- C-c C-a should find solution `lemma p`

data Ps : N → Set where
  []  : Ps z
  _∷_ : {n : N} → Ps n → P n → Ps (s n)

test₂ : {n : N} → P n → Ps (f n) → Ps (s (f n))
test₂ p ps = {! lemma !}  -- C-c C-a should find solution `ps ∷ lemma p`

-- Postponed constraints that turn out unsolvable make a candidate fail.
-- Here, lemma p would need f z = f n.

test₃ : {n : N} → P z → P (f n)
test₃ p = {! lemma !}  -- Expected: No solution found
