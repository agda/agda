-- {-# OPTIONS -v term:20 #-}
module Issue787 where

data ⊥ : Set where

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

data Rat' {X : Set} : List (List X) → List X → Set where
  cons : ∀{ss x xs} → Rat' ((x ∷ xs) ∷ ss) xs → Rat' ss (x ∷ xs)

bad : {X : Set} (xs : List X) (acc : List (List X)) (p : Rat' acc xs) → ⊥
bad .(x ∷ xs) acc (cons {ss = .acc} {x = x} {xs = xs} p) =
 bad (x ∷ xs) acc (cons {ss = acc} {x = x} {xs = xs} p)

-- Andreas, 2013-02-18
-- This should give a termination error.
-- It did pass up to today because of the idempotency check
-- excluded bad calls with embedded sub-matrices.
-- Disabling matrix-shaped orders, which do not have a formal semantics
-- anyway, bring the termination problem to Agda's attention.
