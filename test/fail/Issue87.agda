module Issue87 where

data I : Set where

data D : I -> Set where
  d : forall {i} (x : D i) -> D i

bar : forall {i} -> D i -> D i -> D i
bar (d x) (d     y) with y
bar (d x) (d {i} y) | z = d {i} y

-- Panic: unbound variable i
-- when checking that the expression i has type I
