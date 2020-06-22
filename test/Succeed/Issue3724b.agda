{-# OPTIONS --prop --allow-unsolved-metas #-}

data ⊤ : Prop where
  tt : ⊤

data A : ⊤ → Set where
  a : (x : ⊤) → A x

f : A tt → ⊤
f (a x) = {!!}
