module IrrelevantLambda where

postulate
  A : Set
  P : A -> Set

f : _ -> Set
f = λ .x -> P x
-- fails because irrelevant lambda may not introduce relevant function type