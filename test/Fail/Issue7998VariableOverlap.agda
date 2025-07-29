-- Andreas, 2025-07-15, issue #7998.
-- `overlap` only makes sense for fields, so it should not be parsed
-- (and silently dumped) in variable declarations.

variable
  overlap {{X}} : Set

-- WAS: `overlap` silently ignored.

-- Expected error: [ParseError]
-- overlap<ERROR>  {{X}} : Set
