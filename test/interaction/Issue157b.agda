
module Issue157b where

postulate
  A B : Set
  R   : A → B → Set
  err : ∀ {a b} → R a b → R b