-- Andreas, 2017-01-24, issue #2429
-- ..-annotation in lambdas should be taken seriously

-- A ≤ ..A ≤ .A
-- (.A → B) ≤ (..A → B) ≤ A → B

should-fail : ∀{A B : Set} → (.A → B) → (.A → B)
should-fail f = λ ..a → f a

-- Expected error:
-- Found a non-strict lambda where a irrelevant lambda was expected
-- when checking that the expression λ ..a → f a has type ..A → .B

-- Note: Since A and B are not in scope, they are printed as .A and .B
-- This makes this error message super confusing.

-- New error after removing dots from out-of-scope variables:
-- Found a non-strict lambda where a irrelevant lambda was expected
-- when checking that the expression λ ..a → f a has type .A → B
