module FlatDomInequality where


postulate
  A : Set


g : A → A
g x = x

-- this is fine
h : (@♭ x : A) → A
h = g

-- this should fail, although the error message should be improved.
q : A → A
q = h
