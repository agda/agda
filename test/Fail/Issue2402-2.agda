-- Andreas, 2017-01-13, issue #2402
-- Error message: incomplete pattern matching

open import Common.Bool

module _ (A B C D E F G H I J K L M O P Q R S T U V W X Y Z : Set) where

test2 : Bool → Bool
test2 x with true
test2 true | x = ?

-- WAS: Reports:
-- Incomplete pattern matching for .IncompletePattern.with-56.
-- Missing cases:
--   .IncompletePattern.with-56 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ false
-- when checking the definition of with-56
-- That's total bogus!

-- Expected:

-- Incomplete pattern matching for .Issue2402-2.with-56.
-- Missing cases:
--   test2 false | w
-- when checking the definition of with-56
