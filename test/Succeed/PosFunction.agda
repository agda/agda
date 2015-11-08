module PosFunction where

data Functor : Set1 where
  |Id|  : Functor
  |K|   : Set -> Functor
  _|+|_ : Functor -> Functor -> Functor
  _|x|_ : Functor -> Functor -> Functor

data _⊕_ (A B : Set) : Set where
  inl : A -> A ⊕ B
  inr : B -> A ⊕ B

data _×_ (A B : Set) : Set where
  _,_ : A -> B -> A × B

-- The positivity checker can see that [_] is positive in its second argument.
[_] : Functor -> Set -> Set
[ |Id|    ] X = X
[ |K| A   ] X = A
[ F |+| G ] X = [ F ] X ⊕ [ G ] X
[ F |x| G ] X = [ F ] X × [ G ] X

data μ_ (F : Functor) : Set where
  <_> : [ F ] (μ F) -> μ F
