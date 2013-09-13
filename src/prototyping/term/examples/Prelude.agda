
module Prelude where

data _==_ {A : Set}(x : A) : A → Set where
  refl : x == x

J : {A : Set} {x y : A} (P : (x y : A) → x == y -> Set) →
    (∀ z → P z z refl) → (p : x == y) → P x y p
J P h refl = h _
