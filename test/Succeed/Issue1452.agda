module _ {A : Set} (P : A → Set) where

  postulate
    bla : {x : A} {{_ : P x}} → Set → Set

  test :  {x : A} {{_ : P x}} → Set → Set
  test B = bla B
