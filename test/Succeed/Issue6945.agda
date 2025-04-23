-- Andreas, 2024-03-02, issue #6945:
-- Reported and original testcase by Matthias Hutzler.
-- Missing warnings for useless private and other useless block.
-- Andreas, 2025-03-29, issue #7765: useless private in where block

postulate
  Nat : Set

module M where

  f : Nat → Nat
  f x = y
    where
      private  -- useless, Andreas, 2025-03-29, issue #7765
        module _ where
          private  -- not useless
            y = x
          z = y
        y = z

  private  -- useless
    syntax f x = [ x ]

h : Nat → Nat
h x = M.[ y ]  -- This is accepted, showing that the [ ] syntax is not private.
  module H where
    private  -- not useless
      y = x

postulate
  _#_ : Nat → Nat → Nat

private  -- useless
  infixl 5 _#_

private  -- useless
  {-# POLARITY _#_ + - #-}
  {-# POLARITY Nat     #-}  -- Andreas, 2024-10-10 this useless pragma should be ignored (#7546).

-- Expected: Warning about useless private.

---------------------------------------------------------------------------
-- Similar warnings for other blocks.

postulate A : Set
abstract  -- useless
  infix 0 A

postulate I : Set
instance  -- useless
  infix 0 I

postulate M : Set
macro  -- useless
  infix 0 M

postulate O : Set
opaque  -- useless
  infix 0 O

---------------------------------------------------------------------------
-- Merging in other test cases for UselessPrivate

-- * test/Succeed/LetPrivate
_ =
  let
    private  -- useless
      x : Set _
      x = Set
  in x

-- * test/Fail/UselessPrivateImport

private  -- useless
  open import Agda.Builtin.Equality

-- * test/Fail/UselessPrivateImport2

private  -- useless
  open import Common.Issue481ParametrizedModule Set

-- * test/Fail/UselessPrivateImportAs

private  -- useless
  import Agda.Builtin.Bool as B

-- * test/Fail/UselessPrivatePragma

postulate Char : Set

private  -- useless
  {-# BUILTIN CHAR Char #-}

-- * test/Fail/UselessPrivatePrivate

private  -- useless
  private
    postulate
      PP : Set

-- * test/Fail/Issue476a issue #476

Issue476 : Set₁
private  -- useless
  Issue476 = Set
