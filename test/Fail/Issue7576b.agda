-- Andreas, 2024-10-27 issue #7576
-- reported and testcase by Mario Carneiro
--
-- Just a data signature can be produced with reflection.
-- This used to trigger an internal error during serialization.
--
-- Andreas, 2026-10-19, issue #8851:
-- A data signature without definition is now rejected.

open import Common.Reflection

unquoteDecl data D =
  declareData D 0 (quoteTerm Set)
