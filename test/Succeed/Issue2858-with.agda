open import Agda.Builtin.Nat

interleaved mutual

  plus : Nat → Nat → Nat
  mult : Nat → Nat → Nat

  -- base case
  mult 0 n = 0
  plus 0 n = n

  -- inductive case. The fun clauses with an ellipsis belong to mult
  mult (suc m) n with mult m n
  ... | p with plus p n
  ... | q = q
  plus (suc m) n = suc (plus m n)

open import Agda.Builtin.Equality

proof : ∀ m n → mult (suc m) n ≡ plus (mult m n) n
proof m n with mult m n
... | p with plus p n
... | q = refl
