-- Andreas, 2018-10-18, re #2757
-- Runtime-irrelevance analogue to issue #2640

{-# OPTIONS --erasure #-}

-- {-# OPTIONS -v tc.lhs.unify:65 #-}
-- {-# OPTIONS -v tc.irr:20 #-}
-- {-# OPTIONS -v tc:30 #-}
-- {-# OPTIONS -v treeless:20 #-}

open import Common.Prelude

data D : (n : Nat) → Set where
  c : (m : Nat) → D m

test : (@0 n : Nat) → D n → Nat
test n (c m) = m

-- WAS: Should be rejected (projecting a forced argument).

main = printNat (test 142 (c _))

-- WAS: The generated Haskell program segfaults.

-- Andreas, 2026-01-02, should succeed.
