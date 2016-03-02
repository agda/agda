-- Andreas, 2016-02-09, should not record sections have all hidden parameters?

module _ (A : Set) where

  record R : Set where
    postulate
      P : (a : A) → Set

  -- Records have some magic to make record parameters hidden
  -- in record section.
  -- This leads to an error in @checkInternal@.
  -- Should the parent parameters alse be hidden in the record section?

  record Fails (a : A) : Set where

    T = (w p : R.P _ a) → Set -- well-formed

    f : R.P _ a → Set
    f p with p
    ... | _ = A

-- ERROR:
-- Expected a hidden argument, but found a visible argument
-- when checking that the type (w p : R.P _ a) → Set of the generated
-- with function is well-formed

-- Should succeed.
