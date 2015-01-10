-- Andreas, 2014-01-09, illegal double hiding info in typed bindings.

postulate
  ok  : ({A} : Set) → Set
  bad : {{A} : Set} → Set
