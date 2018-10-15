-- Andreas, 2018-10-13, re issue #3244
--
-- Error should be raised when --no-prop and trying to use Prop
-- (universe-polymorphic or not).

{-# OPTIONS --no-prop #-}

data False {ℓ} : Prop ℓ where

-- Expected: Failure with error message
