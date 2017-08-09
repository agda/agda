-- Christian Sattler, 2017-08-05
-- Nullary extended lambdas are useful in the interaction mode
-- for case splitting on the result inside an expression.
module NullaryExtendedLambda where

f : {A : Set} → A → A
f a = λ { → a }

g : {A : Set} → A → A
g a = λ where
  → a
