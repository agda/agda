-- Andreas, 2020-03-27, issue #4534
-- Better error message for quote.

open import Agda.Builtin.Reflection

_ : Name
_ = quote Set

-- Can only quote defined names, but encountered Set
-- when checking that the expression quote Set has type Name
