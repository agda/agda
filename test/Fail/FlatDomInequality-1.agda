module FlatDomInequality-1 where

postulate
  A : Set

g : A → A
g x = x

h : (@♭ x : A) → A
h = g
