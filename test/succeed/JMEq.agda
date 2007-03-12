
module JMEq where

data _==_ {A : Set}(x : A) : {B : Set}(y : B) -> Set where
  refl : x == x

subst : {A : Set}{x y : A}(P : A -> Set) -> x == y -> P x -> P y
subst {A} P refl px = px

