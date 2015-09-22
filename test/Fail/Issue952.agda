
postulate
  f : {A B : Set₁} (C : Set) → A → B → C

module _ (A B C : Set) where
  test : (X : Set) → Set → Set → X
  test = f { A₁ = Set } { B₁ = Set }
