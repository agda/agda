{-# OPTIONS --cubical #-}

open import Agda.Builtin.Cubical.Path

-- Works:

data Truncate (A : Set) : Set where
  [_] : A → Truncate A
  sq  : ∀{x y} (p q : PathP (λ _  → Truncate A) x y)
         → PathP (λ _ → PathP (λ _ → Truncate A) x y) p q

data Truncat (A : Set) : Set where
  [_] : A → Truncat A
  sq  : ∀{x y : Truncat A} (p q : x ≡ y) → p ≡ q

-- Fails:

data Trunc (A : Set) : Set where
  [_] : A → Trunc A
  sq  : ∀{x y} (p q : PathP (λ _  → Trunc A) x y)
         → PathP _ p q

-- The failure is expected, but it shouldn't give a non-obligated
-- equality constraint as the reason for the failure.
