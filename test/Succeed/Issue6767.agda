-- Andreas, 2023-08-20, issue #6767, reported and testcase by omelkonian
--
-- Forcing translation had a spurious __IMPOSSIBLE__ in connection with literals.
-- (Regression in 2.6.2).

open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality

-- predicates P and Q
data P : Nat → Set where
  mkP : Nat → P 0

Q : Nat → Set
Q n = P (go n)
  where go : Nat → Nat
        go _ = 0

substQ : ∀ {n} → 0 ≡ n → Q 0 → Q n
substQ refl q = q

-- relation between predicates
data _~_ : P 0 → (Σ Nat λ n → P n) → Set where
  mk : ∀ {n} {p : Q 0} (eq : 0 ≡ n) → mkP n ~ (_ , substQ eq p)

-- simple pattern match causes internal error, but goes away with `--no-forcing`
testPatternMatch-~ : ∀ {p q} → p ~ q → Nat
testPatternMatch-~ (mk eq) = 0
