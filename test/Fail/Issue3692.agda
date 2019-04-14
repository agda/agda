-- Andreas, 2019-04-13, issue #3692, reported by xekoukou

-- Feature #1086, omission of trivially absurd clauses,
-- caused wrong polarity computation.

-- {-# OPTIONS -v tc.polarity:20 #-}
-- {-# OPTIONS -v tc.cover.missing:100 #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

data _≤_ : (m n : Nat) → Set where
  z≤n : ∀ {n}                 → zero  ≤ n
  s≤s : ∀ {m n} (m≤n : m ≤ n) → suc m ≤ suc n

≤-pred : ∀ {m n} → suc m ≤ suc n → m ≤ n
≤-pred (s≤s m≤n) = m≤n

data Fin : Nat → Set where
  fzero : (n : Nat) → Fin (suc n)
  fsuc  : (n : Nat) (i : Fin n) → Fin (suc n)

inject≤ : ∀ m n → Fin m → m ≤ n → Fin n
inject≤ m (suc n) (fzero _)   le = fzero _
inject≤ m (suc n) (fsuc m' i) le = fsuc _ (inject≤ m' n i (≤-pred le))
-- Agda 2.6.0 accepts inject≤ without the following clauses,
-- leading to faulty acceptance of test below.
-- inject≤ (suc _) zero (fzero _) ()
-- inject≤ (suc _) zero (fsuc _ _) ()

test : ∀ {m n} (i : Fin m) (m≤n m≤n' : m ≤ n)
     → inject≤ m n i m≤n ≡ inject≤ m n i m≤n'
test i m≤n m≤n' = refl

-- WAS: succeeded because of wrong polarity for inject≤

-- Expected error:

-- m≤n != m≤n' of type m ≤ n
-- when checking that the expression refl has type
-- inject≤ m n i m≤n ≡ inject≤ m n i m≤n'
