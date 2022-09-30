-- Andreas, 2022-09-30, issue #6066
-- Warn also about redundant "pattern" attribute
-- if eta for a record was inferred, rather than declared.

record D : Set1 where
  pattern
  field
    foo : Set

match : D → Set
match record{ foo = A } = A

comatch : Set → D
comatch A .D.foo = A

-- Expected warning:
-- `pattern' attribute ignored for eta record
