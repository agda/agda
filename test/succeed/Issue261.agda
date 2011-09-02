
module Issue261 where

postulate
  List : Set → Set
  nil : ∀ A → List A
  Nat : Set

works-now : List Nat
works-now with nil _
... | xs = xs
