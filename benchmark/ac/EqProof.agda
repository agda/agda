
module EqProof
  { A : Set }
  ( _==_ : A -> A -> Set )
  (refl  : {x : A} -> x == x)
  (trans : {x y z : A} -> x == y -> y == z -> x == z)
  where

  infix 2 eqProof>_
  infixl 2 _===_
  infix 3 _by_

  eqProof>_ : (x : A) -> x == x
  eqProof> x = refl

  _===_ : {x y z : A} -> x == y -> y == z -> x == z
  xy === yz = trans xy yz

  _by_ : {x : A}(y : A) -> x == y -> x == y
  y by eq = eq


