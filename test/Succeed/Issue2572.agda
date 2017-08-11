
record Unit : Set where
  constructor unit

module S {A : Set} where
  id : {A : Set} → A → A
  id a = a

module T {A : Set} = S

Sid : (A : Set) → A → A
Sid A = S.id {A = Unit} {A = A}

Tid : (A : Set) → A → A
Tid A = T.id {A = Unit} {A = Unit} {A = A}
