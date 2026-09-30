-- {-# OPTIONS -v 10 #-}
-- {-# OPTIONS -v auto:100 #-}

postulate A : Set

X : Set₂
X = (P : Set₁) → (A → P) → P

foo : X → X
foo x P f = {!!}

-- Invoke Agsy in the hole above. Result:
--
--   Set != Set₁
--   when checking that the expression A has type Set₁
--
-- The error message points to A in the definition of X.

-- x : (P : Set₁) → (A → P) → P
-- P : Set₁
-- f : A → P
-- ? : P

-- Agsy constructs  f (x A (λ z → z))  which is ill-typed
-- as A is in the wrong universe.
-- It should take universe levels into account.

-- Temporary fix: discard wrong solution, Agsy returns nothing.
