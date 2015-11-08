-- Andreas, 2014-09-23
-- Syntax declaration for overloaded constructor.

module _ where

module A where

  syntax c x = ⟦ x ⟧

  data D2 (A : Set) : Set where
    c : A → D2 A

  data D1 : Set where
    c : D1

open A

test : D2 D1
test = ⟦ c ⟧

-- Should work.
