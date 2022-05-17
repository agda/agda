-- {-# OPTIONS --show-implicit #-}
{-# OPTIONS --sized-types #-}

module _ where

open import Common.Size

data Either (A B : Set) : Set where
  left  : A → Either A B
  right : B → Either A B

caseEither : ∀{A B C : Set} → Either A B → (A → C) → (B → C) → C
caseEither (left  a) l r = l a
caseEither (right b) l r = r b

data Nat {i : Size} : Set where
  zero : Nat
  suc  : {i' : Size< i} → Nat {i'} → Nat

-- subtraction is non size increasing
sub : {size : Size} → Nat {size} → Nat {∞} → Nat {size}
sub zero    n       = zero
sub (suc m) zero    = suc m
sub (suc m) (suc n) = sub m n

-- div' m n  computes  ceiling(m/(n+1))
div' : {size : Size} → Nat {size} → Nat → Nat {size}
div' zero    n = zero
div' (suc m) n = suc (div' (sub m n) n)

-- one can use sized types as if they were not sized
-- sizes default to ∞

add : Nat → Nat → Nat
add (zero ) n = n
add (suc m) n = suc (add m n)

nisse : {i : Size} → Nat {i} → Nat {i}
nisse zero          = zero
nisse (suc zero)    = suc zero
nisse (suc (suc n)) = suc zero

-- symmetric difference
-- @diff n m@ returns @left (n - m)@ if @n@ is bigger, otherwise @right (m - n)@
diff : ∀{i j} → Nat {i} → Nat {j} → Either (Nat {i}) (Nat {j})
diff zero    m       = right m
diff (suc n) zero    = left (suc n)
diff (suc n) (suc m) = diff n m

module Case where
  gcd : ∀{i j} → Nat {i} → Nat {j} → Nat
  gcd zero    m       = m
  gcd (suc n) zero    = suc n
  gcd (suc n) (suc m) = caseEither (diff n m)
    (λ n' → gcd n' (suc m))
    (λ m' → gcd (suc n) m')

module With where
  gcd : ∀{i j} → Nat {i} → Nat {j} → Nat
  gcd zero    m       = m
  gcd (suc n) zero    = suc n
  gcd (suc n) (suc m) with diff n m
  ... | left  n' = gcd n' (suc m)
  ... | right m' = gcd (suc n) m'






NatInfty = Nat {∞}

{-# BUILTIN NATURAL  NatInfty  #-}
-- {-# BUILTIN NATPLUS     add       #-} -- not accepted
