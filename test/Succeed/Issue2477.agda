-- Andreas, 2017-02-27, issue #2477

{-# OPTIONS --show-irrelevant --sized-types #-}

open import Agda.Builtin.Size
open import Agda.Builtin.Nat using (suc) renaming (Nat to ℕ)

_+_ : Size → ℕ → Size
s + 0 = s
s + suc n = ↑ (s + n)

data Nat : Size → Set where
  zero  :  ∀ i → Nat (i + 1)
  suc   :  ∀ i → Nat i → Nat (i + 1)
  -- i + 1 should be reduced to ↑ i
  -- to make Nat monotone in its size argument

pred : ∀ i → Nat i → Nat i
pred .(i + 1) (zero i)   =  zero i
pred .(i + 1) (suc i x)  =  x

-- Should succeed
