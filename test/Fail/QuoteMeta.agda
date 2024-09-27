-- Andreas, 2024-09-27

open import Agda.Builtin.Nat
open import Agda.Builtin.Reflection

_ : Name
_ = quote ?

-- `quote' expects an unambiguous defined name,
-- but here the argument is a metavariable
-- when checking that the expression quote 42 has type Name
