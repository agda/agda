-- Andreas, 2017-03-27 fixing regression #2472

-- Auto should be applicable also outside function clauses

-- {-# OPTIONS -v auto:100 #-}

open import Agda.Primitive

test : Set {!!}
test = Set

-- Auto should succeed on this goal
