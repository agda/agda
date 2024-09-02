-- Andreas, 2024-07-23
-- Trigger error WrongAnnotationInLambda

{-# OPTIONS --guarded #-}

test : (A : Set) → A
test = λ (@tick A) → A

-- Expected error:
--
-- Wrong annotation in lambda
-- when checking that the expression λ (@tick A) → A has type (A : Set) → A
