{-# OPTIONS --no-keep-pattern-variables #-}

postulate
  A : Set
  B : Set
  t : B

data C : (b : B) → Set

foo : (b : B) → C b → B

data C where
  c : (x : C t) → C (foo t x)

foo b x = {!x!}

-- Case split on x should produce:
-- foo .(foo t x) (c x) = ?
