{-# OPTIONS --allow-unsolved-metas #-}

open import Agda.Builtin.Nat

data Tick : Nat → Set where
  tick : ∀ {n} → Tick (suc n)

data Tensor : ∀ n → Tick n → Set where
  ss : ∀ {n} → Tensor (1 + n) tick

tensor→a : ∀ {n s} → Tensor n s → Set
tensor→a x = {!!}
