-- {-# OPTIONS -v tc.lhs.unify:100 #-}
-- Reported by project member adamgundry, 2012-10-26

-- I was trying to extend Conor's KIPLING technique (Outrageous but
-- Meaningful Coincidences, WGP 2010) which depends on indexing a
-- syntax by functions, when I hit this problem:

module Issue738 where

open import Common.Equality

data U : Set where
  a : U
  b : U

-- works, with explicit equality:

module Param where

  data D (f : U → U) : Set where
    da : (f ≡ λ x → a) → D f
    db : (f ≡ λ x → b) → D f

  app : ∀ {A B : Set}{f g : A → B} → f ≡ g → ∀ x → f x ≡ g x
  app refl x = refl

  fu : D (λ x → a) → Set
  fu (da refl) = U
  fu (db p) with app p a
  ... | ()

-- original formulation:

module Index where

  data Foo : (U -> U) -> Set where
    mka : Foo (\ x -> a)
    mkb : Foo (\ x -> b)

  foo : Foo (\ x -> a) -> Set
  foo mka = ?

-- This gives the error message:

-- -- Cannot decide whether there should be a case for the constructor
-- -- mkb, since the unification gets stuck on unifying the inferred
-- -- indices
-- --   [λ x → b]
-- -- with the expected indices
-- --   [λ x → a]
-- -- when checking the definition of foo

-- But these indices cannot be unified (a and b are constants) so it
-- should be possible to exclude this case.  Could we improve the
-- unifier to notice this?

-- Andreas, 2012-10-29 No, because if the domain type is empty,
-- these two lambdas cannot be disunified
