{-# OPTIONS --rewriting #-}

data Nat : Set where
  zero : Nat
  suc : Nat → Nat
{-# BUILTIN NATURAL Nat #-}

_+_ : Nat → Nat → Nat
zero + m = m
suc n + m = suc (n + m)
{-# BUILTIN NATPLUS _+_ #-} -- Without this, the internal error disappears.

postulate
  _≡_ : Nat → Nat → Set
{-# BUILTIN REWRITE _≡_ #-}

postulate
  a b n : Nat
  Q : Nat → Set
  R : (m n : Nat) → Q (m + n) → Set
  +S : (n + a) ≡ b
{-# REWRITE +S #-}

variable
  m : Nat -- Explicitly quantifying over m, the internal error disappears.

postulate
  bug : (q : Q n) → R m n q
