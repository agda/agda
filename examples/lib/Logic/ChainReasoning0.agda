
module Logic.ChainReasoning0
  ( _==_ : {A, B : Set} -> A -> B -> Set )
  (refl  : {A : Set}(x : A) -> x == x)
  (trans : {A, B, C : Set}(x : A)(y : B)(z : C) -> x == y -> y == z -> x == z)
  where

  infix 2 chain>_
  infixl 2 _===_
  infix 3 _by_

  chain>_ : {A : Set}(x : A) -> x == x
  chain> x = refl _

  _===_ : {A, B, C : Set}{x : A}{y : B}{z : C} -> x == y -> y == z -> x == z
  xy === yz = trans _ _ _ xy yz

  _by_ : {A, B : Set}{x : A}(y : B) -> x == y -> x == y
  y by eq = eq


