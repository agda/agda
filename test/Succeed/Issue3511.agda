{-# OPTIONS --cubical --allow-unsolved-metas #-}

open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Nat

pred : Nat → Nat
pred (suc n) = n
pred zero = zero

data [0-1] : Set where
  𝟎 𝟏 : [0-1]
  int : 𝟎 ≡ 𝟏

-- The following holes can be filled, so they should not cause a
-- typechecking failure.

0=x : ∀ i → 𝟎 ≡ int i
0=x i = \ j → int {!!}

si : {n m : Nat} → suc n ≡ suc m → n ≡ m
si p i = pred (p {!!})
