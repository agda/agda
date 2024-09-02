
it : {A : Set} → ⦃ A ⦄ → A
it ⦃ x ⦄ = x

postulate
  X : Set
  C : Set → Set
  c : {A : Set} → ⦃ C A ⦄ → A

opaque
  Y : Set
  Y = X

instance
  postulate CY : C Y

opaque
  unfolding Y

  works : Y
  works = c ⦃ it ⦄

  fails : Y
  fails = c
