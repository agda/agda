
module _ where

record LinearOrderStr (D : Set) : Set₁ where
  no-eta-equality
  field
    _<_ : D -> D -> Set

open LinearOrderStr {{...}}

postulate
  D : Set

module _ {{O : LinearOrderStr D}} where
  abstract
    broken : {b c : D} -> (b < c) -> b < c
    broken {b} {c} b<c = b<c
      where
      b<c2 : b < c
      b<c2 = b<c
