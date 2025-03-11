-- Test case by Calvin Lee

data ⊤ : Set where
  tt : ⊤

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

_ : List ⊤
_ = tt ∷_
