-- Andreas, 2024-09-27

open import Agda.Builtin.Nat
open import Agda.Builtin.Reflection

_ : Name
_ = quote 42

-- `quote' expects an unambiguous defined name,
-- but here the argument is a literal: 42
-- when checking that the expression quote 42 has type Name
