-- Andreas, 2016-09-13, issue #2177, reported by Andres
--
-- Check me with -v check.ranges:100

postulate A : Set

-- Was an internal error when loading Agda.Primitive
-- (because of range outside the current file).
