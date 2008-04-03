

module Lib.Id where

data _≡_ {A : Set}(x : A) : A -> Set where
  refl : x ≡ x

cong : {A B : Set}(f : A -> B){x y : A} -> x ≡ y -> f x ≡ f y
cong f refl = refl

subst : {A : Set}(P : A -> Set){x y : A} -> x ≡ y -> P y -> P x
subst P refl px = px