{-# OPTIONS --allow-unsolved-metas #-}

-- Andreas, 2016-12-19, issue #2344, reported by oinkium, shrunk by Ulf
-- The function Agda.TypeChecking.Telescope.permuteTel
-- used in the unifier was buggy.

-- {-# OPTIONS -v tc.meta:25 #-}
-- {-# OPTIONS -v tc.lhs:10 #-}
-- {-# OPTIONS -v tc.lhs.unify:100 #-}
-- {-# OPTIONS -v tc.cover:20 #-}

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

data Fin : Nat → Set where
  zero : ∀ n → Fin (suc n)

postulate
  T     : Nat → Set
  mkT   : ∀{l} → T l
  toNat : ∀ m → Fin m → Nat

-- The underscore in the type signature is originally dependent on A,X,i
-- but then pruned to be dependent on A,X only.
-- The unifier had a problem with this.
toNat-injective : ∀ (A : Set) X i → T (toNat _ i)  -- Yellow expected.
toNat-injective A X (zero n) = mkT

-- Should pass.

-- Jesper, 2017-08-13: This test case now fails since instantiation
-- of metavariables during case splitting was disabled (see #2621).
