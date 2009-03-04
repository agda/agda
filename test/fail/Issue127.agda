
module Issue127 where

data C : Set where
  c : C
  d : C

F : C → Set → Set
F c = λ A → A
F d = λ A → A

data D : C → Set where
  d : (x : C) → F x (D x) → D x

--                                               .-< no longer
-- The following non-well-founded definition is / seemingly accepted by
-- Agda:

∞ : (x : C) → D x
∞ x = d x (d x (∞ x))
