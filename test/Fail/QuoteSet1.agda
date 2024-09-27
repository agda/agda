-- Andreas, 2024-09-27, issue #7514
-- `quote` rejects universes with a numeric suffix

open import Agda.Builtin.Reflection

_ : Name
_ = quote Set1

-- `quote' expects an unambiguous defined name,
-- but here the argument is a compound expression
-- when checking that the expression quote Set₁ has type Name
