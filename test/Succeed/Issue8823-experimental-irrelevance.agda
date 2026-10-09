-- Andreas, 2026-10-09, issue #8823
-- Variant of Issue8823 with --experimental-irrelevance.
-- Regression introduced by the fix of #8811 (PR #8812),
-- found in agda-unimath (univalent-combinatorics.injective-maps).

-- PR #8812 made the occurs check treat the sort annotation of a type
-- as irrelevant.  In irrelevant positions, the occurs check does not
-- reduce terms, so it did not record the meta in an offending
-- occurrence like @_s p@ (in the sort annotation of a Pi type) as a
-- blocker.  The postponed assignment of _B was then not retried
-- when _s was solved.

{-# OPTIONS --experimental-irrelevance #-}

postulate
  D : Set → Set

Dec : Set → Set
Dec A = D A

postulate
  iff : {A B : Set} → (A → B) → (B → A) → Dec A → Dec B
  A   : Set
  P   : A → A → Set

test : Dec ((x y : A) → P x y) → Dec ({x y : A} → P x y)
test d = iff (λ p {x} {y} → p x y) (λ p x y → p) d

-- Error was:
-- Cannot instantiate the metavariable _B_15 to solution P x y
-- since it contains the variable x
-- which is not in scope of the metavariable
-- when checking that the expression λ x y → p has type
-- (x y : A) → P x y
