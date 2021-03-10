-- Andreas, 2016-07-17 issue 2101

-- It should be possible to place a single function with a where block
-- inside `abstract`.

-- This will work if type signatures inside a where-block
-- are considered private, since in private type signatures,
-- abstract definitions are transparent.
-- (Unlike in public type signatures.)

record Wrap (A : Set) : Set where
  field unwrap : A

postulate
  P : ∀{A : Set} → A → Set

module AbstractPrivate (A : Set) where
  abstract
    B : Set
    B = Wrap A

    postulate
      b : B

    private -- this no longer (since #418) make abstract defs transparent in type signatures
      postulate
        test : P (Wrap.unwrap b) -- should no longer succeed
