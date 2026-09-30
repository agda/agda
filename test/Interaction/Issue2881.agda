{-# OPTIONS --sized-types #-}

open import Agda.Builtin.Size

postulate
  X : Set
  P : X → Set
  Q : (x : X) → P x → Set

data D (i : Size) : Set where
  c : D i

f : (i : Size) → D i → X
f i c = {!!}

g : (x : X) (y : P x) → Q x y → Q x y
g _ _ q = q

h : (i : Size) (n : D i) → P (f i n)
h _ c = {!!}

k : (n : D ∞) → Q (f ∞ n) (h ∞ n)
k _ = g _ (h _ {!!}) _
