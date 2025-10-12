-- Andreas, 2017-03-27, issue #2183
-- Better error message for splitting on non-visible dot pattern.
-- Andreas, 2025-10-12, issue #7941
-- Allow splitting on non-visible dot pattern.

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

data Fin : Nat → Set where
  fzero : ∀ n → Fin (suc n)

test : ∀ n (i : Fin n) → Set
test n (fzero m) = {!n!}  -- C-c C-c

-- WAS error:
-- Cannot split on variable n, because it is bound to term  suc m
-- when checking that the expression ? has type Set

-- Behavior since 2025-10-12: succeed and give
-- test .(suc m) (fzero m) = {!!}
