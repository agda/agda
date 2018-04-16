-- Andreas, 2018-04-16, inspired by issue #3032 reported by sattlerc

-- A termination issue without visible recursion.

postulate
  A : Set
  B : Set
  t : B

mutual

  data C : (b : B) → Set where
    c : (x : C t) → C (foo t bar)

  postulate
    bar : C t

  foo : (b : B) → C b → B
  foo y (c x) = y

-- Should not termination check.
-- y is actually "foo t bar" here, a potentially non-terminating recursive call.
