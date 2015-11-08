    module _ where

    module A where

      data D : Set₁ where
        !_ : Set → D

      infix 3 !_

    data C : Set₁ where
      #_ : A.D → C

    infix 2 #_

    module B where

      data D : Set₁ where
        !_ : C → D

      infix 1 !_

    open A
    open B

    ok₁ : B.D → B.D
    ok₁ (! # X) = ! # X

    ok₂ : C → C
    ok₂ (# ! X) = # ! X
