  postulate
    F : Set₂ → Set₃
    G : Set₁ → Set₂
    H : Set₀ → Set₁

  infix 1 F
  infix 2 G
  infix 3 H

  syntax F x = ! x
  syntax G x = # x
  syntax H x = ! x

  ok₁ : Set₀ → Set₂
  ok₁ X = # ! X

  ok₂ : Set₁ → Set₃
  ok₂ X = ! # X
