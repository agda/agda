-- Andreas, 2020-03-27, issue #4534
-- Better error message for quote.

open import Agda.Builtin.Reflection

quote₀ : Set → Name
quote₀ X = quote X

-- Cannot quote a variable X
-- when checking that the expression quote X has type Name
