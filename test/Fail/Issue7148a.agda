-- Andreas, 2024-02-26, issue #7148.
-- See also #1342.

module _ (A : Set) (a : A → A) where

test : Set
test with (λ (x : A) → a x)
... | _ = A

-- Should fail as we cannot with-abstract over module parameter.
