
data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

{-# BUILTIN NATURAL Nat #-}

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

pred : Nat → Nat
pred zero = zero
pred (suc n) = n

{-# NON_TERMINATING #-}
loop : Nat → Nat
loop zero = zero
loop n = loop (pred n)

-- Non-terminating functions reduce when evaluated at top-level,
-- but not in a hole.
hole : Set
hole = {!!}
