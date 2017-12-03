-- Andreas, 2017-12-03, issue #2826, reported by Snicksi, shrunk by sattlerc

data A : Set where
  a : A

data B : Set where
  b : (x : A) → B

foo : B → B
foo s with a
-- WAS: case splitting produces repeated variables in pattern
foo s | x = {!s!}

-- Expected: Something like the following
-- foo (b x₁) | x = {!!}
