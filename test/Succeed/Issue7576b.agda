-- Andreas, 2024-10-27 issue #7576
-- reported and testcase by Mario Carneiro
--
-- Just a data signature can be produced with reflection.
-- This used to trigger an internal error during serialization.

open import Common.Reflection

unquoteDecl data D =
  declareData D 0 (quoteTerm Set)

-- This data type without a definition can be used like a postulate.

id : D → D
id x = x
