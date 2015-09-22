-- Andreas, 2014-06-16

data D A : Set where
  c : {x : A} → A → D A

f : ∀(A : Set) → D A → Set
f A (c a b) = D A

-- Expected error:
-- The constructor c expects 2 arguments (including hidden ones), but
-- has been given 3 (including hidden ones)
-- when checking that the pattern c a b has type D A
