-- Andreas, 2025-04-05, re issue #2513, do not allow conflicting relevance info.

postulate
  Foo : .{@relevant A : Set} → A

-- Expected error: [ParseError]
-- Conflicting relevance information
