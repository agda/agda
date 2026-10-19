-- Andreas, 2025-10-03, issue #8122
-- Wrong argument order in generated helper function.
-- Regression introduced by #8104.

data T : Set where
  bin : (t u : T) → T

Foo : T → Set
Foo (bin t u) = {! Aux t u (Foo t) (Foo u) !} -- C-c C-h

-- WAS:      Aux : Set → Set → T → T → Set
-- Expected: Aux : T → T → Set → Set → Set
