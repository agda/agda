
module _ where

record R : Set₁ where
  field x : Set

g : Set₁

module M (r : R) where
  open R r
  f = x

g = R
