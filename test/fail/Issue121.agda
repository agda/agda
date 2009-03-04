
module Issue121 where

bad : Set → Set
bad A = A → A

data Bool : Set where
  true  : Bool
  false : Bool

F : Bool → Set → Set
F true  = bad
F false = λ A → A

data D : Set where
  nop : (b : Bool) → F b D → D

