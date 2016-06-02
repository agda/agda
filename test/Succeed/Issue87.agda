module Issue87 where

data I : Set where

data D : I -> Set where
  d : forall {i} (x : D i) -> D i

bar : forall {i} -> D i -> D i -> D i
bar (d x) (d     y) with y
bar (d x) (d {i} y) | z = d {i} y

-- ERROR WAS:
-- Panic: unbound variable i
-- when checking that the expression i has type I

-- Andreas, 2016-06-02
-- This looks weird, but is accepted currently:
test : ∀ i → D i → D i → D i
test .i (d {i} x) (d {.i} y) with y
test .i (d {j} x) (d {i} y) | _ = d {i} y
-- Note the {j}!
