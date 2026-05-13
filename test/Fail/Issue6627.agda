-- CheckArguments call exposes dummy checkArguments return type
module Issue6627 where

record Foo : Set₁ where
  field foo : Set
record Bar ⦃ _ : Foo ⦄ : Set where
postulate
  i : Foo
  b : Bar ⦃ i ⦄

open Bar b

-- Error was:
-- No instance of type Foo was found in scope.
-- when checking that b is a valid argument to a function of type
-- ⦃ _ = z : Foo ⦄ → .Bar → "dummyType: __DUMMY_TYPE__, called at ..."

-- Expected error: [InstanceNoCandidate]
-- No instance of type Foo was found in scope.
-- when checking that b is a valid argument to a function accepting
-- arguments of type ⦃ _ = z : Foo ⦄ (r : Bar)
