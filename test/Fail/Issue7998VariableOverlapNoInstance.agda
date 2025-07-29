-- Andreas, 2025-07-15, issue #7998.
-- Bad error for `overlap` in variable declarations.

variable
  overlap X : Set

-- Was error: [ParseError]
-- The 'overlap' keyword only applies to instance fields (fields marked with {{ }})

-- Expected error: [ParseError]
-- overlap<ERROR>  X : Set
