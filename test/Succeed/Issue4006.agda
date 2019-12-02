
data I : Set where
  i : I

variable
  x : I

abstract

  data D : I → Set where
    d : D i

  accepted : {x : I} → D x → Set₁
  accepted {x = i} d = Set

  rejected : D x → Set₁
  rejected {x = i} d = Set
