postulate
  A : Set
  x : A
  f : (P : A → Set) → P x

g : (P : ((A → A) → A) → Set) → P (λ h → h x)
g P = f (λ y → P ?)
