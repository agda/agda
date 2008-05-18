
module Chain
    { A : Set }
    (_==_  : A -> A -> Set )
    (refl  : (x : A) -> x == x)
    (trans : (x y z : A) -> x == y -> y == z -> x == z)
  where

  infix 2 chain>_
  infixl 2 _===_
  infix 3 _by_

  chain>_ : (x : A) -> x == x
  chain> x = refl _

  _===_ : {x y z : A} -> x == y -> y == z -> x == z
  xy === yz = trans _ _ _ xy yz

  _by_ : {x : A}(y : A) -> x == y -> x == y
  y by eq = eq

