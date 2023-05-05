{-# OPTIONS --erasure #-}

-- Andreas, 2018-10-16, wrong quantity in lambda-abstraction

applyErased : {@0 A B : Set} → (@0 A → B) → @0 A → B
applyErased f x = f x

test : {A : Set} → A → A
test x = applyErased (λ (@ω y) → y) x

-- Expected error:
--
-- Wrong quantity annotation in lambda abstraction.
--
-- Current error (because @ω as default quantity is ignored):
--
-- Variable y is declared erased, so it cannot be used here
-- when checking that the expression y has type _B_7
