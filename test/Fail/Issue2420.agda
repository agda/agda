
module _ where

module M where

record S : Set₁ where
  open M
  field
    F1 : Set
    F2 : {!!}
