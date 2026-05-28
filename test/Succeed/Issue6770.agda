-- Andreas, 2026-04-30, issue #6770, reported by Orestis Melkonian
-- Shrunk test case by Szumi Xi

postulate A : Set

module M (x : A) where
  postulate a : A

variable x : A

module _ (open M x) where
  _ : A
  _ = a

-- WAS: error [UnequalTypes]
-- The type
--   (genTel : Issue6770..GeneralizeTel) → A
-- is not a subtype of
--   A
-- when checking that the expression a has type A

-- Should succeed.
