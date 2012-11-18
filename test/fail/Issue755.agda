
module Issue755 where

open import Common.Prelude renaming (Nat to ℕ)
open import Common.Equality

abstract
  foo : ℕ → ℕ
  foo x = zero

bar : foo zero ≡ foo (suc zero) → foo zero ≡ foo (suc zero)
bar refl = refl
-- 0 != 1 of type ℕ
-- when checking that the pattern refl has type
-- foo zero ≡ foo (suc zero)
