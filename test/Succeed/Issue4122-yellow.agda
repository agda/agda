{-# OPTIONS --prop #-}

data _≡_ {A : Set} (a : A) : A → Set where
  refl : a ≡ a

postulate
  funextP : {A : Prop} {B : A → Set} {f g : (a : A) → B a} (h : (x : A) → f x ≡ g x) → f ≡ g

test      : {A : Prop} {B : A → Set} {f g : (a : A) → B a} (h : (x : A) → f x ≡ g x) → f ≡ g
test h = funextP h
