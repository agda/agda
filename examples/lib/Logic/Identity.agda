
module Logic.Identity where

open import Logic.Equivalence
open import Logic.Base

infix 20 _≡_ _≢_

data _≡_ {A : Set}(x : A) : A -> Set where
  refl : x ≡ x

subst : {A : Set}(P : A -> Set){x y : A} -> x ≡ y -> P y -> P x
subst P {x} .{x} refl px = px

sym : {A : Set}{x y : A} -> x ≡ y -> y ≡ x
sym {A} refl = refl

trans : {A : Set}{x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
trans {A} refl xz = xz

cong : {A B : Set}(f : A -> B){x y : A} -> x ≡ y -> f x ≡ f y
cong {A} f refl = refl

cong2 : {A B C : Set}(f : A -> B -> C){x z : A}{y w : B} -> x ≡ z -> y ≡ w -> f x y ≡ f z w
cong2 {A}{B} f refl refl = refl

Equiv : {A : Set} -> Equivalence A
Equiv = record
        { _==_  = _≡_
        ; refl  = \x -> refl
        ; sym   = \x y -> sym
        ; trans = \x y z -> trans
        }

_≢_ : {A : Set} -> A -> A -> Set
x ≢ y = ¬ (x ≡ y)

sym≢ : {A : Set}{x y : A} -> x ≢ y -> y ≢ x
sym≢ np p = np (sym p)

