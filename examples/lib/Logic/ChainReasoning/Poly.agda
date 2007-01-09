
module Logic.ChainReasoning.Poly
  ( _==_ : {A : Set} -> A -> A -> Set )
  (refl  : {A : Set}(x : A) -> x == x)
  (trans : {A : Set}(x y z : A) -> x == y -> y == z -> x == z)
  where

  infix 2 chain>_
  infixl 2 _===_
  infix 3 _by_

  chain>_ : {A : Set}(x : A) -> x == x
  chain> x = refl _

  _===_ : {A : Set}{x y z : A} -> x == y -> y == z -> x == z
  xy === yz = trans _ _ _ xy yz

  _by_ : {A : Set}{x : A}(y : A) -> x == y -> x == y
  y by eq = eq


