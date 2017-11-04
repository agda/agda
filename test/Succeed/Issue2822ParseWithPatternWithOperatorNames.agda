-- Andreas, 2017-11-04, while refactoring for issue #2822

-- This is a test case for a with-pattern that overloads operator names

postulate
  A : Set
  _<_ _>_ : A → A → A

data D : Set where
  c : A → A → D

postulate
  f : D

bla : D → Set
bla (c < >) = A

test : Set
test with f
test | c < > = A
  -- This triggers a call to Agda.Syntax.Concrete.Operators.validConPattern, case WithP

-- Should parse.
