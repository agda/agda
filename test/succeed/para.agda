
module para where

module Top (A B : Set) where

  module A (C D : Set) where
    postulate f : A -> B -> C -> D

  module B (E F : Set) = A F E renaming (f to j)

  postulate h : A -> B

  module C (G H : Set) where

    module D = B G H

    g' : A -> B
    g' = h

    g : A -> H -> G
    g x y = D.j x (h x) y

module Bottom where

  postulate
    Nat : Set
    zero : Nat

  module D = Top Nat Nat
  module C = D.C Nat Nat

  x : Nat
  x = C.g zero zero

