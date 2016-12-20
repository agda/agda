record R : Set₁ where
  field
    _! : Set → Set

open R

F : Set → Set
F ! = !
