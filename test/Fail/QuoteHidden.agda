-- Andreas, 2024-09-27

open import Agda.Builtin.Reflection

_ : Name
_ = quote { Set }

-- `quote' expects an unambiguous defined name,
-- but here the argument is implicit
