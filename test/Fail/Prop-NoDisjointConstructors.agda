{-# OPTIONS --prop #-}

data TestProp : Prop where
  p₁ p₂ : TestProp

data _≡Prop_ {A : Prop} (x : A) : A → Set where
  refl : x ≡Prop x

p₁≢p₂ : {P : Prop} → p₁ ≡Prop p₂ → P
p₁≢p₂ ()
