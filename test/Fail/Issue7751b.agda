module Issue7751b where

module M (X : Set) where
  record X' : Set where

Bad : Set
open M Bad
Bad = X'
