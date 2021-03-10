{-# OPTIONS --without-K #-}

postulate w/e : Set

data _==_ {A : Set} : A → A → Set where
  idp : {a : A} → a == a

data Square {A : Set} {a : A} : {b c d : A} (p : a == b) (q : c == d) (r : a == c) (s : b == d) → Set where
  ids : Square {a = a} idp idp idp idp

J1 : {A : Set} {a : A} {p : a == a} → Square p idp idp idp → Set
J1 ids = w/e

J2 : {A : Set} {a : A} {p : a == a} → Square idp p idp idp → Set
J2 ids = w/e

J3 : {A : Set} {a : A} {p : a == a} → Square idp idp p idp → Set
J3 ids = w/e

J4 : {A : Set} {a : A} {p : a == a} → Square idp idp idp p → Set
J4 ids = w/e
