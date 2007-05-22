
module RecordInParModule (a : Set) where

record Setoid : Set1 where
  el : Set

postulate
  S : Setoid
  A : Setoid.el S

