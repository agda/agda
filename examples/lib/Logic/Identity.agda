
module Logic.Identity where

import Logic.Equivalence
open Logic.Equivalence

infix 40 _≡_

data _≡_ {A : Set}(x : A) : A -> Set where
  refl : x ≡ x

subst : {A : Set}(P : A -> Set){x y : A} -> x ≡ y -> P y -> P x
subst P {x} .{x} refl px = px

sym : {A : Set}{x y : A} -> x ≡ y -> y ≡ x
sym {A} refl = refl

trans : {A : Set}{x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
trans {A} refl xz = xz

cong : {A : Set}(f : A -> A){x y : A} -> x ≡ y -> f x ≡ f y
cong {A} f refl = refl

cong2 : {A : Set}(f : A -> A -> A){x y z w : A} -> x ≡ z -> y ≡ w -> f x y ≡ f z w
cong2 {A} f refl refl = refl

Equiv : {A : Set} -> Equivalence A
Equiv = equiv _≡_ (\x -> refl) (\x y -> sym) (\x y z -> trans)

