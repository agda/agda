-- 2017-11-01, issue #2668 reported by brprice
--
--     This seems to have been fixed in 2.5.3 (specifically, commit
--     8518b8e seems to have solved this, along with #2727 and #2726)

-- {-# OPTIONS -v tc.mod.apply:20 #-}
-- {-# OPTIONS -v tc.proj.like:40 #-}
-- {-# OPTIONS -v tc.signature:60 #-}

-- {-# OPTIONS -v tc.with:60 #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

module _ (Q : Set) where -- parameter needed to trigger issue

-- has to pattern match: `badRefl _ = refl` typechecks
badRefl : (n : Nat) → n ≡ n
badRefl zero = refl
badRefl (suc n) = refl

-- has to wrap: `Wrap = Nat` (and changing uses of wrap) typechecks

data Wrap : Set where
  wrap  : (n : Nat) → Wrap

record Rec (A : Set) : Set where
  field
    recW : (m : Nat) → Wrap

  foo : A → Wrap → Wrap
  foo _ (wrap i) = recW i

Thin : Rec Nat
Thin = record { recW = wrap }

module Th = Rec Thin

test : ∀ (th : Nat)(t : Wrap)
   → Th.foo th t ≡ Th.foo th t

  -- If we don't go via Th, it typechecks
  --   → Rec.foo Thin th t ≡ Rec.foo Thin th t

-- test = {!Rec.foo!}
test th t with badRefl th
... | p = refl

-- ERROR WAS:
-- Expected a hidden argument, but found a visible argument
-- when checking that the type
--   (Q : Set) (th : Nat) → th ≡ th → (t : Wrap) →
--     Rec.foo (record { recW = wrap }) th t ≡
--     Rec.foo (record { recW = wrap }) th t
-- of the generated with function is well-formed

-- Should succeed
