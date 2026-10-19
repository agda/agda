-- Andreas, 2025-10-18, issue #8144

record A : Set₁
open A           -- This open is placed too early
record A where
  field f : Set
g : A → Set
g = f

-- Expected error: [NoSuchModule]
-- No module A in scope---but a record type of that name is in scope
-- whose record module is either not defined yet or hidden (note that
-- records defined in a `mutual' block cannot be opened in the same
-- block)
