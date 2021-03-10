-- Andreas, 2020-04-15, issue #4586
-- Better error for invalid let pattern.

test : Set₁
test = let () = Set
       in  Set

-- WAS:
-- Set₁ should be empty, but that's not obvious to me
-- when checking that the pattern () has type Set₁

-- EXPECTED:
-- Not a valid let pattern
-- when scope checking let () = Set in Set
