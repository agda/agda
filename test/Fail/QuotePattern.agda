-- Andreas, 2024-09-27

open import Agda.Builtin.Nat
open import Agda.Builtin.Reflection

postulate
  F : Name → Name
  X : Name

test : Name → Set₁
test (quote (F X)) = Set

-- `quote' expects an unambiguous defined name, but here the argument is a compound pattern
-- when scope checking the left-hand side test (quote (F X)) in the definition of test
