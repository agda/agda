-- Andreas, 2016-11-19 issue #2308

-- Since fix of #2197, in mutual blocks, records are no-eta-equality
-- until the positivity checker has run.
-- Thus, the record pattern translation might not kick in.

-- Now, there is another pass of record pattern translation
-- after the mutual block has finished.

data Unit : Set where
  unit : Unit

mutual -- needed to trigger issue

  record R : Set where  -- needs to be in mutual block
    pattern; constructor wrap
    field f : Unit

  G : R → Set
  G (wrap _) = Unit -- match on wrap needed

test : (x : R) → G x → Set₁
test _ unit = Set

-- ERROR WAS:
-- Type mismatch
-- when checking that the pattern unit has type G x

-- Should succeed.
