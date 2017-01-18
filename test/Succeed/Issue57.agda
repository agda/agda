-- Andreas, 2017-01-18, issue #57
-- reported by Nisse 2008-03-26

data Unit : Set where
  unit : Unit

foo : Unit → Unit
foo m with m
foo _ | x@unit with x
foo _ | x@unit | _ = x

test : Unit → Unit
test m with m
test _ | x@unit with x
... | _ = x
