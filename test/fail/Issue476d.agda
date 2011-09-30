-- Private signatures
module Issue476d where

module M where
  private
    record R : Set₁

  record R where
    field X : Set

Q : Set₁
Q = M.R