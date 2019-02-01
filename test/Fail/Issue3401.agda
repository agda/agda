
module _ {I : Set} where

postulate
  f : ∀ {T : I → Set} {i} → T i → Set

variable
  i : I
  T : I → Set
  v : T i

t : f v
t = {!!}
