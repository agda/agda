    module _ where

    module A where

      postulate
        !_ : Set₂ → Set₃

      infix 1 !_

    module B where

      postulate
        !_ : Set₀ → Set₁

      infix 3 !_

    open A
    open B

    postulate
      #_ : Set₁ → Set₂

    infix 2 #_

    ok₁ : Set₁ → Set₃
    ok₁ X = ! # X

    ok₂ : Set₀ → Set₂
    ok₂ X = # ! X
