-- Internal error in coverage checker.
module Issue505 where

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

_+_ : Nat → Nat → Nat
zero  + m = m
suc n + m = suc (n + m)

data Split : Nat → Nat → Set where
  1x1 : Split (suc zero) (suc zero)
  _∣_ : ∀ {a b c} → Split a b → Split a c → Split a (b + c)
  _/_ : ∀ {a b c} → Split b a → Split c a → Split (b + c) a

data ⊤ : Set where
  tt : ⊤

theorem : ∀ {a b} → (split : Split a b) → ⊤
theorem 1x1 = tt
theorem {suc a} .{_} (l ∣ r) = tt
theorem {zero } .{_} (l ∣ r) = tt
theorem (l / r) = tt
