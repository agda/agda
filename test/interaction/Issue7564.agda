{-# OPTIONS --cubical #-}
open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Unit

postulate
  A : Set

data Circle : Set where
  base : Circle
  loop : base ≡ base

data T : Circle → Set where
  zero : T base
  suc : T base → T base
  p : PathP (λ i → T (loop i)) zero (suc zero)

F : Circle → Set
F base = A → A
-- F (loop i) = ⊤ -- this throws the expected type error: A → A != ⊤ of type Set
F (loop i) = {! ⊤ !} -- C-c C-SPC should give the same type error (#7564)

f : (x : Circle) → T x → F x
f .base zero = {! !}
f .base (suc t) = {! !}
f .(loop i) (p i) = {! !} -- this line is needed to trigger #7564
