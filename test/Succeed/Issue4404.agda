{-# OPTIONS --cubical #-}

open import Agda.Builtin.Cubical.Path

data D : Set where
  c : D

data E : Set where
  c : (x y : E) → x ≡ y

postulate
  A : Set
  f : (x y : E) → x ≡ y → (u v : A) → u ≡ v

works : E → A
works (c x y i) = f x y (E.c x y) (works x) (works y) i

fails : E → A
fails (c x y i) = f x y (  c x y) (fails x) (fails y) i
