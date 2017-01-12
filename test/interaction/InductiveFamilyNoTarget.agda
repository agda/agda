-- Andreas, 2017-01-12

data D {A : Set} : A → Set where
  c : (a : A) → D {!!}  -- fill with a
  d : (a : A) → {!!}  -- fill with D a
