{-# OPTIONS --allow-unsolved-metas #-}

postulate
  A : Set

data Unit : Set where
  unit : Unit

F : Unit → Set
F unit = A

postulate
  P : {A : Set} → A → Set
  Q : ∀ {x} → F x → Set
  f : ∀ {x} {y : F x} (z : Q y) → P z

variable
  x : Unit
  y : F x

g : (z : Q y) → P z
g z with f z
... | p = p
