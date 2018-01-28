
postulate
  A : Set
  f : A → A

mutual

  F : A → Set
  F x = D (f x)

  data D : A → Set where
    c : (x : A) → F x

G : (x : A) → D x → Set₁
G _ (c _) = Set
