-- Andreas, 2025-10-18, issue #8144 reported by Matthew Daggitt

mutual
  record A : Set₁ where
    field f : Set
  open A
  g : A → Set
  g = f

-- WAS: error: [NoSuchModule] No module A in scope
-- This was deemed confusing as the record A appears to be fully defined.
-- But this actually desugars to:
--
--   record A : Set
--   open A
--   record A where ...
--
-- Thus, the record is not defined yet when attempted to be opened

-- Expected error: [NoSuchModule]
-- No module A in scope---but a record type of that name is in scope
-- whose record module is either not defined yet or hidden (note that
-- records defined in a `mutual' block cannot be opened in the same
-- block)
