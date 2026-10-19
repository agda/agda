-- Andreas, 2026-10-19, issue #8851
-- Declared but undefined data type and undeclared constructor.

module Issue8851-data where
open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit

unquoteDecl data D constructor c = declareData D 0 (agda-sort (lit 0))
