-- Andreas, 2015-08-27 Rewrite rules in parametrized modules are fine.
-- Jesper, 2015-10-14 Semantics of rewrite rules in parametrized modules has
--                    changed (see issue 1652)

{-# OPTIONS --rewriting #-}

open import Common.Nat
open import Common.Equality

{-# BUILTIN REWRITE _≡_ #-}

module _ (y z : Nat) where

  assoc+ : ∀ x → (x + y) + z ≡ x + (y + z)
  assoc+ zero = refl
  assoc+ (suc x) rewrite assoc+ x = refl

{-# REWRITE assoc+ #-}  -- NOT the same as without indentation

test : ∀{x y} → (x + 0) + y ≡ x + y
test = refl
