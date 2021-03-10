-- Andreas, 2020-03-18, issue 4518, reported by strangeglyph

-- Better error message when parsing of LHS fails

open import Agda.Builtin.Nat using (Nat) -- forgot to import constructors

postulate
  foo : Nat

test : Set₁
test with foo
... | zero  = Set
... | suc n = Set

-- ERROR:
-- Could not parse the left-hand side test | suc n
-- NEW INFORMATION:
-- Problematic expression: (suc n)
