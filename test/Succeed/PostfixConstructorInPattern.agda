-- Andreas, 2015-11-28  Check that postfix constructors are fine.
-- There was a TODO in Agda.Syntax.Concrete.Operators which claimed
-- there would be an ambiguity between `true` applied to variable `wrap`
-- and (_wrap true), and arity of constructors would have to be checked.
-- Parsing works fine, so I removed this TODO.

data Bool : Set where true false : Bool

record Wrap (A : Set) : Set where
  constructor _wrap
  field wrapped : A

test : Wrap Bool → Set
test (true wrap) = Bool
test (false wrap) = Bool

test2 : {A : Set} → Wrap A → A
test2 y = let x wrap = y in x
