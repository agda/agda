module _ where

module A where

  infixr 5 _∷_

  data D : Set₂ where
    []  : D
    _∷_ : Set₁ → D → D

module B where

  infix 5 _∷_

  data D : Set₂ where
    _∷_ : Set₁ → Set₁ → D

open A
open B

foo : A.D
foo = Set ∷ []

bar : B.D
bar = Set ∷ Set
