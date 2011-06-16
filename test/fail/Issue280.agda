
module Issue280 where

data PreModel (C : Set) (M : C → Set) : Set → Set where
  model : (c : C) → PreModel C M (M c)

reflect : (C : Set)(M : C → Set) → PreModel C M C → C
reflect .(M c) M (model c) = c

