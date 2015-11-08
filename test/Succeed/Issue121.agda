
module Issue121 where

id : Set → Set
id A = A

data Bool : Set where
  true  : Bool
  false : Bool

F : Bool → Set → Set
F true  = id
F false = id

G : Bool → Set → Set
G true = id
G false = λ A → A

data D : Set where
  nop : (b : Bool) → F b D → D
  bop : (b : Bool) → G b D → D
