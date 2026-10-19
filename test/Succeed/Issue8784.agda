-- Andreas, 2026-09-27, issue #8784
-- Report and test case by Ulrik Buchholtz.
-- Regression in occurs check affecting --cohesion.

{-# OPTIONS --cohesion #-}

module _ where

postulate
  A     : Set
  k♯    : (@♯ x : A) → A
  k♭    : (@♭ x : A) → A
  apply : (A → A) → A

-- Accepted.
direct : A
direct = apply (λ a → k♯ (k♭ a))

record R (x : A) : Set where
  field out : A

D : Set
D = R (apply (λ a → k♯ (k♭ a)))

test : D → A
test r = R.out r

-- Error was:
-- Failed to solve the following constraints:
--   apply (λ a → k♯ (k♭ a)) =< _x_12 : A

-- Should succeed.
