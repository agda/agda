module UnknownImplicitInstance where

it : {A : Set} {{a : A}} → A
it {{a}} = a

postulate
  B : Set
  instance b : B
  f : {A : Set₁} {{a : A}} → A

x : Set
x = f
