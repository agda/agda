
module LF where

data Zero : Set where

record One : Set where

★ : One
★ = record {}

One-elim : (C : One -> Set) -> C ★ -> (a : One) -> C a
One-elim C h _ = h

One-elim₁ : (C : One -> Set1) -> C ★ -> (a : One) -> C a
One-elim₁ C h _ = h

-- data One' : Set1 where
--   ★' : One'

data Two : Set where
  ★₀ : Two
  ★₁ : Two

case₂ : {A : Set1} -> Two -> A -> A -> A
case₂ ★₀ x y = x
case₂ ★₁ x y = y

data _+_ (A : Set)(B : Set) : Set where
  inl : A -> A + B
  inr : B -> A + B

record _×_ (A : Set)(B : A -> Set) : Set where
  field
    π₀ : A
    π₁ : B π₀

open _×_ public

_,_ : {A : Set}{B : A -> Set}(a : A) -> B a -> A × B
x , y = record { π₀ = x; π₁ = y }

_*_ : (A B : Set) -> Set
A * B = A × \_ -> B

-- data _×'_ (A : Set)(B : A -> Set1) : Set1 where
--   _,'_ : (a : A) -> B a -> A ×' B
-- 
-- π₀' : {A : Set}{B : A -> Set1} -> A ×' B -> A
-- π₀' (a ,' b) = a
-- 
-- π₁' : {A : Set}{B : A -> Set1}(p : A ×' B) -> B (π₀' p)
-- π₁' (a ,' b) = b


