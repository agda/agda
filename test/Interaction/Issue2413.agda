-- Andreas, 2017-01-18, issue #2413
-- As-patterns of variable patterns

data Bool : Set where
  true false : Bool

test : Bool → Bool
test x@y = {!x!}  -- split on x

test1 : Bool → Bool
test1 x@_ = {!x!} -- split on x

test2 : Bool → Bool
test2 x@y = {!y!} -- split on y
