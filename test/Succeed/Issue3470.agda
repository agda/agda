
postulate
  A : Set
  P : A → Set
  Q : ∀{a} → P a → Set

variable  -- WORKS if replaced by postulate
  a : A

module _ (p : P a) (let q = p) where

  postulate r : Q q

-- Panic: unbound variable q (id: 18@787003719158301342)
-- when checking that the expression q has type P _a_12
