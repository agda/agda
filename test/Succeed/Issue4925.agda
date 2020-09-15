
import Agda.Builtin.FromNat as FromNat -- not opened
open import Agda.Builtin.Nat

-- Since fromNat is not in scope unqualified this should work without
-- a Number instance for Nat.
x : Nat
x = 0

-- Renaming fromNat should not make a difference
open FromNat renaming (fromNat to fromℕ)
open import Agda.Builtin.Unit

data MyNat : Set where
  mkNat : Nat → MyNat

instance
  numMyNat : Number MyNat
  numMyNat .Number.Constraint _ = ⊤
  numMyNat .fromℕ n = mkNat n

y : MyNat
y = 1
