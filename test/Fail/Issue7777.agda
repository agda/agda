-- Andreas, 2025-04-05, re issue #7777
-- Make sure we report conflicting information when we allow both
-- traditional relevance annotations ('.' and '..') and
-- and attribute-style relevance annotations ('@irr' etc.).

postulate
  P : .Set → Set₁
  test : .{@shape-irrelevant x : Set} → P x

-- Expected error: [ParseError]
-- Conflicting relevance information
