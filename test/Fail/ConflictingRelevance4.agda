-- Andreas, 2025-04-05, re issue #2513, do not allow conflicting relevance info.

postulate
  Foo : ∀ {A : Set} {P : .A → Set} .(@relevant x) → P x

-- Expected error: [ParseError]
-- Conflicting attribute: @relevant
