-- Andreas, 2026-09-24
-- Example constructed by Claude to demonstrate
-- that the positivity checker loses information
-- in copies created by module application.

{-# OPTIONS --polarity #-}

module _ where

Id : @++ Set → Set
Id X = X

module M (@++ A : Set) where
  data Wrap : Set where
    wrap : A → Wrap

module Works where
  mutual

    W : Set → Set
    W A = M.Wrap (Id A)

    -- This is accepted by the positivity checker:
    data T : Set where
      node : W T → T

-- If we wedge in a module application, the positivity checker used to lose
-- information about the arguments of the copy.

mutual -- essential

  -- Essential that the module application is inside the mutual block:
  -- argument occurrences are only (re)computed for the definitions of a
  -- mutual block.
  -- For a bare bare module application the positivity check is atm not rerun.
  module N (F : @++ Set → Set) (X : Set) = M (F X)

  -- Essential, if we inline W the positivity checker accepts.
  W : Set → Set
  W A = N.Wrap Id A

  -- This is accepted now that the occurrence analysis of the copy takes the
  -- polarity of F's own argument into account:
  data T : Set where
    node : W T → T

-- Should succeed.
