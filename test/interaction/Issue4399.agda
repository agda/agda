-- Andreas, 2020-01-28, issue #4399, reported by G. Brunerie

postulate
  A : Set

data T : Set where
  tt : T

f : {x : A} {{_ : T}} → A
f {{ p }} = {!p!}

-- Problem was:
-- Splitting on p produced pattern {{_ = tt}}
-- which was interpreted as cubical partial split.

-- Expected:
-- Splitting on p should produce an unnamed pattern.
