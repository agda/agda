
module NotStrictlyPositive where

data False : Set where

data Not (A : Set) : Set where
  not : (A -> False) -> Not A

data Neg (A : Set) : Set where
  neg : Not A -> Neg A

data Bad : Set where
  bad : Neg Bad -> Bad

