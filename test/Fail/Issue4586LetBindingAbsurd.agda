-- Andreas, 2020-04-15, issue #4586
-- Better error message when `let` contains an absurd pattern.

test : Set₁
test = let f ()
       in  Set

-- WAS:
-- Not a valid let-declaration
-- when scope checking let f () in Set

-- EXPECTED:
-- Missing right hand side in let binding
-- when scope checking let f () in Set
