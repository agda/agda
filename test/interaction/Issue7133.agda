
module _ where

open import Agda.Primitive

record Point (A : Set) : Set where
  field
    pt : A

record PointedSet : Set₁ where
  field
    Carrier : Set
    point   : Point Carrier

module _ (sto : PointedSet) where

  foo : Set
  foo = {!!}
