-- Andreas, 2014-01-09, illegal double hiding info in typed bindings.

postulate
  ok  : .(A {B} : Set) → Set
  bad : .(A {.B} : Set) → Set
