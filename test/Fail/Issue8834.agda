-- Andreas, 2026-10-15, issue #8834
-- Report, test case, analysis, and fix suggestion by Andrew Swan.

{-# OPTIONS --cohesion #-}

module Issue8834 where

module M (@♯ A : Set) where

  @♯ B : _
  B = A

  C : Set
  C = B     -- Should be rejected

-- Escaping from sharp polarity would be bad.

Bad : @♯ Set → Set
Bad = M.C
