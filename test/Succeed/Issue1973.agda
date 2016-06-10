-- Andreas, 2016-05-13 Issue 1973 reported by Nisse
-- Problems with parameters to overloaded projections

-- {-# OPTIONS -v tc.proj.amb:100 #-}
-- {-# OPTIONS -v tc.deftype:100 #-}

record R₁ : Set₁ where
  field
    f : Set

open R₁ public

postulate
  F : ∀ {a} → Set a → Set a

module M (_ : Set₁) where

  record R₂ a (G : Set a → Set a) (A : Set a) : Set a where
    field
      f : G A

  open R₂ public

open module N = M Set using (f)

works : ∀ a (A : Set a) → N.R₂ a F A → F A
works a A x = N.R₂.f x

-- WAS:
-- a F !=< F A of type Set
-- when checking that the expression f x has type F A

ill-formed-term-in-error-message : ∀ a (A : Set a) → N.R₂ a F A → F A
ill-formed-term-in-error-message a A x = f x

-- What Agda did here is to copy parameters from the reduced record type
--   M.R₂ Set a F A
-- to the unreduced projection
--   N.R₂.f
-- The number of projections (3) was queried from N.R₂.f, but the projections
-- were taken from  M.R₂ Set a F A.
-- Now, take the original version of the projection,
--   M.R₂.f
-- which accepts 4 parameters, and these are the ones provided by  M.R₂ Set a F A.

-- WAS:
-- An internal error has occurred. Please report this as a bug.
-- Location of the error: src/full/Agda/TypeChecking/Substitute.hs:93

internal-error : (A : Set) → N.R₂ _ F A → F A
internal-error A x = f x

-- should work now.
