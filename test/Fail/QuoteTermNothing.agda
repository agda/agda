-- Andreas, 2024-09-27

open import Agda.Builtin.Reflection

_ : Term
_ = quoteTerm

-- `quoteTerm' expects a single visible argument,
-- but has been given none
-- when checking that the expression quoteTerm has type Term
