-- Andreas, 2020-03-20, issue #4482, reported by gallai
-- Precise range for unexpected implicit argument.

_ : Set → {A : Set} → {B : Set} → {C : Set} → Set
_ = λ { _ {B = B} {A = A} → {!!} }

-- Andreas, 2026-10-22, issue #8739: also mention possible arguments.
-- Expected error: [WrongNamedArgumentInLHS]
-- Unexpected implicit argument named A (possible arguments: C)
-- when checking the clause left hand side
-- .extendedlambda0 _ {B = B} {A = A}
--                                 ^ highlight this
