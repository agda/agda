module Issue6745 where

module M (A : Set₂) where

  opaque
    X : Set₂
    X = A

module N (let open M Set₁) where

  opaque
    unfolding X

    Y : X
    Y = Set
