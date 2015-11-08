
module RecordInParModule (a : Set) where

record Setoid : Set1 where
  field el : Set

postulate
  S : Setoid
  A : Setoid.el S

postulate X : Set

module M (x : X) where
  record R : Set where

module E {x : X} (r : M.R x) where
  open module M' = M.R x r

