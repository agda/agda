
module Chain
    {A : Set}(_==_ : A -> A -> Set)
    (refl : (x : A) -> x == x)
    (trans : (x y z : A) -> x == y -> y == z -> x == z)
  where

infix  2 chain>_
infixl 2 _===_by_
infix  1 _qed

private
  data _≃_ (x y : A) : Set where
    prf : x == y -> x ≃ y

chain>_ : (x : A) -> x ≃ x
chain> x = prf (refl x)

_===_by_ : {x y : A} -> x ≃ y -> (z : A) -> y == z -> x ≃ z
prf p === z by q = prf (trans _ _ _ p q)

_qed : {x y : A} -> x ≃ y -> x == y
prf p qed = p

