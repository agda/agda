module LiftDisplayIntermediate where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat
open Agda.Primitive renaming (Set to Type)

record Foo : Type where
  field
    f : Nat

module _ (f : Nat → Foo) where
  module _ n where
    open Foo (f n) renaming (f to g) public
    -- we get a display form [0] Foo.f (@1 @0) --> g @0

  -- out here, we have [1] Foo.f (@1 @0) --> g @0, with the 'n' argument
  -- of the inner module having become a pattern variable

  _ : g zero ≡ zero
  _ = refl

  -- the nontrivial term above is Foo.f (@0 zero), and should display as g zero
  -- previously, this would fail matching, since @1 (on the pattern) ≠ @0 (on the rhs).
  -- however, note that the lhs of the display form has one more variable than the scope we're trying to use it in!
  -- so really we should match [@1 @0] = [@1 zero], lifting the rhs by 1, which does succeed with @0 := zero
  -- so the error printed should be g zero != zero of type Nat
