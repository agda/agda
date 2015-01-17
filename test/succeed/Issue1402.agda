-- Andreas, 2014-01-17 Issue 1402
-- where clauses after a pointless rewrite

open import Common.Equality

postulate eq : Set1 ≡ Set1

test : Set1
test rewrite eq = bla
  where bla = Set

-- should succeed (or maybe alert the user of the pointless rewrite)
