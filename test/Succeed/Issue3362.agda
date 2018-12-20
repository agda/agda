
postulate
  A : Set
  P : A → Set

variable
  x : A
  y : P x

data D₁ {x : A} : P x → Set where
  z : D₁ y
  s : D₁ y → D₁ y

data D₂ : {x : A} → P x → Set where
  z : D₂ y
  s : D₂ y → D₂ y
