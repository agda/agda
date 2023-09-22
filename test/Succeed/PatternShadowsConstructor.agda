-- Andreas, 2023-09-08, re issue #6829
-- The PatternShadowsConstructor is now a benign warning.

-- {-# OPTIONS -v tc.lhs.shadow:30 #-}

module _ where

---------------------------------------------------------------------------
-- Andreas, 2023-09-08, issue #6829
-- The "pattern variable shadow constructor" alert should not be raised
-- for record constructors that do not allow pattern matching.

module PatternShadowsRecordConstructor where

  module A where

    record B : Set where
      constructor x; no-eta-equality -- no 'pattern' directive here!

    data C : Set where
      c : B → C

  open A using (C; c)

  f : C → C
  f (c x) = c x

  -- Should succeed without warning.

---------------------------------------------------------------------------
-- A matchable record constructor should trigger a warning.

module PatternShadowsRecordConstructor2 where

  module A where

    record B : Set where
      constructor x; no-eta-equality; pattern

    data C : Set where
      c : B → C

  open A using (C; c)

  f : C → C
  f (c x) = c x

  -- Should warn about `x`.

---------------------------------------------------------------------------
-- A matchable record constructor should trigger a warning.

module PatternShadowsRecordConstructor3 where

  module A where

    record B : Set where
      constructor x; eta-equality

    data C : Set where
      c : B → C

  open A using (C; c)

  f : C → C
  f (c x) = c x

  -- Should warn about `x`.

-- ========================================================================
-- Tests moved over from test/Fail/

---------------------------------------------------------------------------

module PatternShadowsConstructor where

  module A where

    data B : Set where
      x : B

    data C : Set where
      c : B → C

  open A using (C; c)

  f : C → C
  f (c x) = c x

  -- Should warn about `x`.

---------------------------------------------------------------------------

module PatternShadowsConstructor2 where

  module A where

    data A (X : Set) : Set where
      c : A X → A X
      x : A X

  open A using (A; c)

  f : ∀ {X} → A X → A X → A X
  f (c y) x = x
  f A.x   _ = A.x

  -- Should warn about `x`.

---------------------------------------------------------------------------

module PatternShadowsConstructor3 where

  data Bool : Set where
    true false : Bool

  module A where

    data B : Set where
      x : B

    data C : Set where
      c : B → C

  open A using (C; c)

  T : Bool → Set
  T true = C → C
  T false = Bool

  f : (b : Bool) → T b
  f true (c x) = c x
  f false = true

  -- Should warn about `x`.

---------------------------------------------------------------------------

module PatternShadowsConstructor4 where

  module A where

    data B : Set where
      x : B

    data C : Set where
      c : B → C

  open A using (C; c)

  record R : Set where
    field
      fst : C → C
      snd : A.B
  open R

  r : R
  fst r (c x) = c x
  snd r       = A.B.x

  -- Should warn about `x`.

---------------------------------------------------------------------------

-- Andreas, 2017-12-01, issue #2859 introduced by parameter-refinement

-- In Agda 2.5.2 any definition by pattern matching in a module
-- with a parameter that shadows a constructor will complain
-- about pattern variables with the same name as a constructor.

-- These are pattern variables added by the parameter-refinement
-- machinery, not user written ones.  Thus, no reason to complain here.

module Issue2859 where

  data D : Set where
    c : D

  module M (c : D) where

    data DD : Set where
      cc : DD

    should-work : DD → Set
    should-work cc = DD

    should-warn : D → D
    should-warn c = c

  -- Expected alert:
  -- The pattern variable c has the same name as the constructor c
  -- when checking the clause test c = c
