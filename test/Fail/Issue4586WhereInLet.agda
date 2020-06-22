-- Andreas, 2020-04-15, issue #4586
-- Better error message when `let` contains a `where` clause.

foo : Set₁
foo = let x = Set
              where y = Set
      in  Set

-- WAS:
-- Not a valid let-declaration
-- when scope checking
-- let x = Set
--       where
--         y = Set
-- in Set

-- EXPECTED:
-- No `where' clauses allowed in let binding
-- when scope checking
-- let x = Set
--       where
--         y = Set
-- in Set
