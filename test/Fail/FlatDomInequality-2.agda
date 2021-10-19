module FlatDomInequality-2 where

postulate
  A : Set

h : (@♭ x : A) → A
h x = x

q : A → A
q = h
