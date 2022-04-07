-- Partly based on code due to Andrea Vezzosi.

{-# OPTIONS --cubical-compatible --safe #-}

open import Agda.Builtin.Bool

data D : Set where
  run-time        : Bool → D
  @0 compile-time : Bool → D

g : D → D
g (run-time x)     = run-time x
g (compile-time x) = compile-time x

h : D → @0 D → D
h (run-time x)     _                = run-time x
h (compile-time x) (run-time y)     = compile-time y
h (compile-time x) (compile-time y) = compile-time x

i : @0 D → D → D
i _                (run-time y)     = run-time y
i (run-time x)     (compile-time y) = compile-time x
i (compile-time x) (compile-time y) = compile-time y

data E (@0 A : Set) : Set where
  c₁ c₂ : E A
  @0 c₃ : A → E A

m : {@0 A : Set} → @0 A → E A → E A
m _ c₁     = c₂
m _ c₂     = c₁
m x (c₃ _) = c₃ x
