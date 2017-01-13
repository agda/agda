-- Andreas, 2017-01-13, issue #2402
-- Error message: incomplete pattern matching

-- {-# OPTIONS -v tc.cover:20 #-}

open import Common.Bool

module _ (A B C D E F G H I J K L M O P Q R S T U V W X Y Z : Set) where

test : Bool → Bool
test true = false

-- Reports:
-- Incomplete pattern matching for test. Missing cases:
--   test _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ false

-- Expected:

-- Incomplete pattern matching for test. Missing cases:
--   test false
