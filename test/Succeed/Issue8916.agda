-- Andreas, 2026-11-14, issue #8916
-- @field@ should be allowed in @opaque@ in the same way as @postulate@ is.
-- Previously, a @field@ inside of an @opaque@ gave a FieldOutsideRecord error.

module Issue8916 where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

record R (A : Set) : Set where
  constructor mkR
  opaque
    field a : A
    b : A
    b = a
    field c : A

-- Construction, projection reduction, and pattern matching work normally.
r : R Nat
r = mkR 1 2

_ : R.a r ≡ 1
_ = refl

_ : R.c r ≡ 2
_ = refl

swap : {A : Set} → R A → R A
swap (mkR a c) = record { a = c; c = a }

_ : R.a (swap r) ≡ 2
_ = refl

-- The internal definition can be used, and unfolds when requested.
b : Nat
b = R.b r

opaque
  unfolding R.b

  _ : b ≡ 1
  _ = refl

-- Nested opaque blocks and dependent fields contribute to the telescope.
record Dependent : Set₁ where
  constructor pack
  opaque
    field Carrier : Set
    Alias : Set
    Alias = Carrier
    opaque
      field value : Alias
      copy : Carrier
      copy = value

p : Dependent
p = pack Nat 3

_ : Dependent.value p ≡ 3
_ = refl

opaque
  unfolding Dependent.copy

  _ : Dependent.copy p ≡ 3
  _ = refl

-- We get a UselessOpaque warning if the only content of an opaque block is a fields.

record UselessOpaque : Set₁ where
  opaque
    field
      S : Set
      s : S

-- warning: -W[no]UselessOpaque
-- This `opaque` block has no effect.
-- when scope checking the declaration
--   opaque
--     unfolding {}
--     S : Set
--     s : S
