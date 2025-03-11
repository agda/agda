{-# OPTIONS --cubical #-}
{-# OPTIONS --no-forcing #-}

open import Agda.Builtin.Nat

data Fin : Nat → Set where
  fzero : ∀ {n} → Fin (suc n)
  fsuc : ∀ {n} → Fin n → Fin (suc n)

postulate
  f : ∀ {n} → Fin n → Fin n

works : ∀ {n} → Fin n → Fin n
works         (fzero {n})  = fzero
works {suc n} (fsuc {n} x) = fsuc (works {n} (f x))

-- WAS: termination error when forcing is off
test : ∀ {n} → Fin n → Fin n
test .{suc n} (fzero {n}) = fzero
test .{suc n} (fsuc {n} x) = fsuc (test {n} (f x))
