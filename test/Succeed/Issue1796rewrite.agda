-- Andreas, 2016-04-14 issue 1796 for rewrite

-- {-# OPTIONS --show-implicit #-}
-- {-# OPTIONS -v tc.size.solve:100 #-}
-- {-# OPTIONS -v tc.with.abstract:40 #-}

{-# OPTIONS --sized-types #-}

open import Common.Size
open import Common.Equality

data Either (A B : Set) : Set where
  left  : A → Either A B
  right : B → Either A B

either : {A B : Set} → Either A B →
  ∀{C : Set} → (A → C) → (B → C) → C
either (left a)  l r = l a
either (right b) l r = r b

data Nat : Size → Set where
  zero : ∀{i} → Nat (↑ i)
  suc  : ∀{i} → Nat i → Nat (↑ i)

primrec : ∀{ℓ} (C : Size → Set ℓ)
     → (z : ∀{i} → C i)
     → (s : ∀{i} → Nat i → C i → C (↑ i))
     → ∀{i} → Nat i → C i
primrec C z s zero    = z
primrec C z s (suc n) = s n (primrec C z s n)

case : ∀{i} → Nat i
     → ∀{ℓ} (C : Size → Set ℓ)
     → (z : ∀{i} → C i)
     → (s : ∀{i} → Nat i → C (↑ i))
     → C i
case n C z s = primrec C z (λ n r → s n) n

diff : ∀{i} → Nat i → ∀{j} → Nat j → Either (Nat i) (Nat j)
diff = primrec (λ i → ∀{j} → Nat j → Either (Nat i) (Nat j))
  -- case zero: the second number is bigger and the difference
  right
  -- case suc n:
  (λ{i} n r m  → case m (λ j → Either (Nat (↑ i)) (Nat j))
    -- subcase zero: the first number (suc n) is bigger and the difference
    (left (suc n))
    -- subcase suc m: recurse on (n,m)
     r)

gcd : ∀{i} → Nat i → ∀{j} → Nat j → Nat ∞
gcd zero m = m
gcd (suc n) zero = suc n
gcd (suc n) (suc m) = either (diff n m)
  (λ n' → gcd n' (suc m))
  (λ m' → gcd (suc n) m')

er : ∀{i} → Nat i → Nat ∞
er zero    = zero
er (suc n) = suc (er n)

diff-diag-erase : ∀{i} (n : Nat i) → diff (er n) (er n) ≡ right zero
diff-diag-erase zero    = refl
diff-diag-erase (suc n) = diff-diag-erase n

gcd-diag-erase : ∀{i} (n : Nat i) → gcd (er n) (er n) ≡ er n
gcd-diag-erase zero = refl
gcd-diag-erase (suc {i} n)
  rewrite diff-diag-erase n
          -- Before fix: diff-diag-erase {i} n.
          -- The {i} was necessary, otherwise rewrite failed
          -- because an unsolved size var prevented abstraction.
        | gcd-diag-erase n = refl
