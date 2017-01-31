-- Andreas, 2017-01-19, issue #2412, raised by bixuanzju

-- Agda should not insert hidden lambdas of possibly empty size types

open import Agda.Builtin.Size

data Nat i : Set where
  zero : Nat i
  suc  : {j : Size< i} (n : Nat j) → Nat i

recNat : (P : (i : Size) (n : Nat i) → Set)
  → (fz : ∀{i} → P i zero)
  → (fs : ∀{i}{j : Size< i} (n : Nat j) → P j n → P i (suc n))
  → ∀{i} (n : Nat i) → P i n
recNat P fz fs zero = fz
recNat P fz fs (suc n) = fs n (recNat P fz fs n)

-- This should pass.
-- Agda should not insert the λ {j : Size< i} → fs in the recursive call to recNat.
