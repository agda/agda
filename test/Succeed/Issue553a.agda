module Issue553a where

data D : Set where
  d₁ d₂ : D

data E : Set where

module M (A : Set) where

  data B : Set where
    b : D → B

  T : B → Set
  T (b d₁) = E
  T (b d₂) = E

open M E

g : (d : D) → T (b d) → D
g d t with d₁
g d t | d′ = d′  -- Unsolved meta-variable, no constraints.
