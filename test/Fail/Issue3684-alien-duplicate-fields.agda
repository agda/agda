-- Andreas, 2020-03-27, re #3684

record R : Set₁ where

_ : R
_ = record { f = Set; f = Set }

-- Should complain about alien fields rather than duplicate fields

-- The record type R does not have the fields f, f
-- when checking that the expression record { f = Set ; f = Set } has type R
