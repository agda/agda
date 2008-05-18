
module Star where

data Star {A : Set}(R : A -> A -> Set) : A -> A -> Set where
  rf   : {x : A} -> Star R x x
  _<>_ : forall {x y z} -> R x y -> Star R y z -> Star R x z
