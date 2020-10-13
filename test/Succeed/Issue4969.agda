data D (A : Set) : Set where
  c : A → D A

postulate
  f : (A : Set) → D A → D A
  P : (A : Set) → D A → Set
  _ : (A : Set) (B : _) (g : A → B) → P _ (f _ (c g))
