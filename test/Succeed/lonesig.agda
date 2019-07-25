f : Set → Set

module _ (A : Set) where

  mutual

    g : Set
    g = h

    h : Set
    h = A

f = g
