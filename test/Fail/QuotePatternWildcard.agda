-- Andreas, 2024-09-27

open import Agda.Builtin.Nat
open import Agda.Builtin.Reflection

test : Name → Set₁
test (quote _) = Set

-- `quote' expects an unambiguous defined name,
-- but here the argument is a wildcard pattern
