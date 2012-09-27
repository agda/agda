{-# OPTIONS --sized-types #-}
-- {-# OPTIONS -v tc.size.solve:100 -v tc.meta.new:50 #-}
module CheckSizeMetaBounds where

open import Common.Size

postulate
  Size< : (_ : Size) → Set
{-# BUILTIN SIZELT Size< #-}

data Nat {i : Size} : Set where
  zero : Nat
  suc  : {j : Size< i} → Nat {j} → Nat

one : Nat
one = suc {i = ∞} zero

data ⊥ : Set where
record ⊤ : Set where

NonZero : Nat → Set
NonZero zero    = ⊥
NonZero (suc n) = ⊤

-- magic conversion must of course fail
magic : {i : Size} → Nat {∞} → Nat {i}
magic zero = zero
magic (suc n) = suc (magic n)

lem : (n : Nat) → NonZero n → NonZero (magic n)
lem (zero)  ()
lem (suc n) _ = _

-- otherwise, we exploit it for an infinite loop
loop : {i : Size} → (x : Nat {i}) → NonZero x → ⊥
loop zero ()
loop (suc {j} n) p = loop {j} (magic one) (lem one _)

bot : ⊥
bot = loop one _

