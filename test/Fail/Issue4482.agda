-- Andreas, 2020-03-20, issue #4482, reported by gallai
-- Precise range for unexpected implicit argument.

_ : Set → {A : Set} → {B : Set} → {C : Set} → Set
_ = λ { _ {B = B} {A = A} → {!!} }

-- Unexpected implicit argument
-- when checking the clause left hand side
-- .extendedlambda0 _ {B = B} {A = A}
--                                 ^ highlight this
