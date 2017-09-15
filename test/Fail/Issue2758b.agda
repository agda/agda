{-# OPTIONS --experimental-irrelevance #-}

open import Agda.Builtin.Bool

data Box (A : Set) : ..(x : A) → Set where
  c : (x : A) → Box A x

unbox : {A : Set} → .(x : A) → Box A x → A
unbox a (c b) = b

postulate
  .b : Bool

b' : Bool
b' = unbox b (c _)
