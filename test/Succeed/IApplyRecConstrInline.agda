{-# OPTIONS --cubical #-}

-- This test case justifies why the clauses for a record value
-- definition need to be available in the state (signature)
-- during the record-to-copatterns translation,
-- at least for Cubical Agda.
--
-- For more context, see the implementation of Agda.TypeChecking.Rules.Def.

module IApplyRecConstrInline where

open import Agda.Builtin.Nat

record Category : Set₁ where
  field
    Ob  : Set
    Hom : Ob → Ob → Set
    id  : ∀ x → Hom x x

postulate X : Set

record H (a b : X) : Set where
  no-eta-equality
  field x y : Nat

{-# INLINE H.constructor #-}

open Category

-- Was: IApplyConfluence.hs __IMPOSSIBLE__
--
-- To inline a constructor in cubical code (even code that doesn't use
-- cubical features) all the resulting fields must be properly tagged
-- with their types.
--
-- The constructor inlining code can only figure out what the type of a
-- field should be if the type of the original clause reduces to the
-- record being constructed.
--
-- The coverage checker does not reduce the type that the original
-- clause is tagged with.

c : Category
c .Ob   = X
c .Hom  = H

-- The coverage checker says the following clause has type c .Hom,
-- but the record constructs H; so the field inliner needs to see c's
-- clauses for this reduction to work.

c .id _ = record { x = 1 ; y = 2 }
