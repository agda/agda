-- Andreas, 2024-09-27

open import Agda.Builtin.Reflection

_ : Term
_ = quoteTerm {{x = Set}}

-- `quoteTerm' expects a single visible argument,
-- but has been given an implicit one
-- when checking that the expression quoteTerm ⦃ x = Set ⦄ has type Term
