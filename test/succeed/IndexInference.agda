
module IndexInference where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

data Vec (A : Set) : Nat -> Set where
  []   : Vec A zero
  _::_ : {n : Nat} -> A -> Vec A n -> Vec A (suc n)

infixr 40 _::_

-- The length of the vector can be inferred from the pattern.
foo : Vec Nat _ -> Nat
foo (a :: b :: c :: []) = c
