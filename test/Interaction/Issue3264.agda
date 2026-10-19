-- Andreas, 2018-10-15, issue #3264 reported by Guillaume Brunerie

-- Refine should not say "cannot refine" just because of a termination error.

f : Set → Set
f A = {!f!}  -- C-c C-r

-- EXPECTED ANSWER:
--
-- ?1 : Set
-- ———— Errors ————————————————————————————————————————————————
-- Termination checking failed for the following functions:
--   f
-- Problematic calls:
--   f (?1 (A = A))
-- when checking that the expression f ? has type Set
