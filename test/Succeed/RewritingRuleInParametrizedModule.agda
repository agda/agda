-- Andreas, 2015-08-27 Rewrite rules in parametrized modules are fine.
-- Jesper, 2015-10-14 Semantics of rewrite rules in parametrized modules has
--                    changed (see issue 1652)
-- Jesper, 2015-11-9  Rewrite rules in parametrized modules are now
--                    generalized to the top-context automatically
-- Andreas, 2017-11-01 Issue #2824: allow BUILTIN REWRITE in preamble

{-# OPTIONS --rewriting #-}

open import Common.Nat
open import Common.Equality

-- Issue #2824: the following pragma is now allowed before the top-level module:

{-# BUILTIN REWRITE _≡_ #-}

module RewritingRuleInParametrizedModule where  -- Top-level module

module M (y z : Nat) where

  assoc+ : ∀ x → (x + y) + z ≡ x + (y + z)
  assoc+ zero = refl
  assoc+ (suc x) rewrite assoc+ x = refl

  {-# REWRITE assoc+ #-}

test : ∀{x y} → (x + 0) + y ≡ x + y
test = refl
