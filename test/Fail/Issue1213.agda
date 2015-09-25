
open import Common.Level

-- Note that this is level-polymorphic
record ⊤ {a} : Set a where
  constructor tt

data ⊥ {a} : Set a where

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

lzero' : ℕ → Level
lzero' zero    = lzero
lzero' (suc n) = lzero ⊔ (lzero' n)

IsZero : (x : ℕ) → Set (lsuc (lzero' x))
IsZero zero = ⊤
IsZero (suc _) = ⊥

test : IsZero (suc _)
test = tt
