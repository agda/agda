{-# OPTIONS --erasure #-}

-- Andreas, 2018-10-16, wrong quantity in lambda-abstraction

applyErased : {@0 A B : Set} → (@0 A → B) → @0 A → B
applyErased f x = f x

test : {A : Set} → A → A
test x = applyErased (λ (@ω y) → y) x

-- Expected error:
--
-- Incorrect quantity annotation in lambda
-- when checking that the expression λ (@ω y) → y has type
-- @0 _A_6 → _B_7
