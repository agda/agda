{-# OPTIONS --erasure #-}

record R (A : Set) : Set where
  field
    x : A

works : (@0 A : Set) → R A → A
works _ record{ x = x } = x

fails : (@0 A : Set) → R A → A
fails = λ (@0 A) → R.x

fails' : (@0 A : Set) → R A → A
fails' = λ (@0 A) r → R.x r

data D (A : Set) : Set where
  c : A → D A

works2 : (@0 A : Set) → A → D A
works2 _ x = c x

fails2 : (@0 A : Set) → A → D A
fails2 A x = c {A = A} x
