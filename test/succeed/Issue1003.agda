-- Andreas, 2013-12-28
-- Reported by jesper.cockx, Dec 20, 2013

-- WAS:  In the following example, there is an unsolved instance
-- argument, but no part of the code is highlighted.

typeof : ∀ {{T : Set}} → T → Set
typeof {{T}} x = T

test : {A : Set} {B : Set} (y : A) → typeof y
test y = y

-- Should solve the instance argument, no constraint should remain.
