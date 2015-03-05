  postulate
    F  : Set₂ → Set₃
    #_ : Set₁ → Set₂
    !_ : Set₀ → Set₁

  infix 1 F
  infix 2 #_
  infix 3 !_

  syntax F x = ! x

  ok₁ : Set₁ → Set₃
  ok₁ X = ! # X

  ok₂ : Set₀ → Set₂
  ok₂ X = # ! X
