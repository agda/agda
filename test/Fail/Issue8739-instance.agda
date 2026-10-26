-- Andreas, 2026-10-22, issue #8739

postulate
  C : Set

f : {X : Set} {{Y Z : C}} → Set → Set
f {{W = W}} B = B

-- Expected error: [WrongNamedArgumentInLHS]
-- Unexpected instance argument named W (possible arguments: Y Z)
