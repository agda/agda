-- Andreas, 2019-11-06, issue #4173, reported and testcase by nad.
-- Allow pattern matching on erased arguments in erased context.

-- {-# OPTIONS -v tc.cover.split:60 #-}

open import Agda.Builtin.Bool

@0 F : @0 Bool → Set₁
F true  = Set
F false = Set

-- Should succeed.

@0 G : @0 Bool → Set₁
G x = {! x !}  -- splitting on x should also succeed
