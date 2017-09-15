{-# OPTIONS --experimental-irrelevance #-}

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

data Box (A : Set) : ..(x : A) → Set where
  c : (x : A) → Box A x

unbox : {A : Set} → .(x : A) → Box A x → A
unbox a (c b) = b

.b : Bool
b = true

b' : Bool
b' = unbox b (c _)
