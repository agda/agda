-- Andreas, 2018-06-14, issue #2513, do not allow conflicting relevance info.

postulate
  Foo : {A : Set} → .(@shape-irrelevant A) → A

-- Should fail.  (Currently: parse error)
