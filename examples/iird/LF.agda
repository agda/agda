
module LF where

data Zero : Set where

data One : Set where
  ★ : One

data One' : Set1 where
  ★' : One'

data Two : Set where
  ★₀ : Two
  ★₁ : Two

case₂ : {A : Set1} -> Two -> A -> A -> A
case₂ ★₀ x y = x
case₂ ★₁ x y = y

data _+_ (A : Set)(B : Set) : Set where
  inl : A -> A + B
  inr : B -> A + B

data _×_ (A : Set)(B : A -> Set) : Set where
  <_|_> : (a : A) -> B a -> A × B

π₀ : {A : Set}{B : A -> Set} -> A × B -> A
π₀ < a | b > = a

π₁ : {A : Set}{B : A -> Set}(p : A × B) -> B (π₀ p)
π₁ < a | b > = b

_*_ : (A B : Set) -> Set
A * B = A × \_ -> B

data _×'_ (A : Set)(B : A -> Set1) : Set1 where
  <_|_>' : (a : A) -> B a -> A ×' B

π₀' : {A : Set}{B : A -> Set1} -> A ×' B -> A
π₀' < a | b >' = a

π₁' : {A : Set}{B : A -> Set1}(p : A ×' B) -> B (π₀' p)
π₁' < a | b >' = b


