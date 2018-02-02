
open import Agda.Builtin.Nat

data D : Set where
  c : D → D

record R : Set where
  constructor mkR
  field f : Nat

f : D → R
f (c x) = mkR zero

f' : D → Nat → R
f' (c x) n = mkR n

postulate
  P  : (A : Set) → A → Set
  g  : (x : D) → P R (f x) → P D x
  g' : (n : Nat) (x : D) → P R (f' x n) → P D x

h : (x : D) → P R (mkR zero) → P D (c x)
h x = g _

h' : (n : Nat) (x : D) → P R (mkR n) → P D (c x)
h' n x = g' n _
