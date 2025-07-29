-- Andreas, 2025-07-15, issue #7998.
-- Instance blocks in variable blocks do not achieve anything,
-- so the user should be alerted of this, at least with a warning.

variable
  instance
    X : Set

-- WAS: `instance` silently ignored.

-- Expected error: [ParseError]
-- instance<ERROR>
--     X : Set
