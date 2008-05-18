
module Graph (Node : Set) where

open import Basics

data Edge : Set where
  edge : Node -> Node -> Edge

Graph : Set
Graph = List Edge

Step : Graph -> Node -> Node -> Set
Step G x y = Elem (edge x y) G

infixr 40 _<>_

data Path (G : Graph) : Node -> Node -> Set where
  nul  : forall {x}     -> Path G x x
  _<>_ : forall {x y z} -> Step G x y -> Path G y z -> Path G x z
