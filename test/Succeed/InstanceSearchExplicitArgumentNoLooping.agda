postulate A : Set

module _ {{a : A}} (f : A → A) where

  g : {{a : A}} → A
  g {{a}} = a

  t : A
  t = g
