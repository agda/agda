-- Andreas, 2020-03-18, issue #4518, reported by strangeglyph
-- Andreas, 2020-06-03, issue #4704, now preserves ellipsis in error

-- Better error message when parsing of LHS fails

open import Agda.Builtin.Nat using (Nat) -- forgot to import constructors

postulate
  foo : Nat

test : Set₁
test with foo
... | zero  = Set
... | suc n = Set

-- ERROR:
-- Could not parse the left-hand side ... | suc n
-- NEW INFORMATION:
-- Problematic expression: (suc n)
