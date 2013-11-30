module Issue919 where

open import Common.Prelude

Zero : Nat → Set
Zero 0 = ⊤
Zero (suc _) = ⊥

test : (n : Nat) {p : Zero n} → Set → Set
test 0            A = A
test (suc _) {()}

-- Horrible error for first clause:
-- Cannot eliminate type Set with pattern {(implicit)} (did you supply
-- too many arguments?)
-- when checking that the pattern zero has type Nat

-- Caused by trailing implicit insertion (see Rules/Def.hs).

-- With trailing implicit insertion switched off, this should work now.
