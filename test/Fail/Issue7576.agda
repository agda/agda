-- Andreas, 2024-10-27, issue #7576
-- reported and test case by Mario Carneiro

open import Common.Reflection

unquoteDecl data D =
  declareData D 1 (quoteTerm Set)

-- Expected error: [Unquote.TooManyParameters]
-- Cannot shave 1 parameters off type Set₀
