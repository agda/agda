-- Andreas, 2026-11-19, issue #8390, report and test by Ode-to-a-Nightingale
-- Discrepancy in float semantics for slow and fast reduction leads to inconsistency

{-# OPTIONS --safe --fast-reduce #-}

module Issue8930 where

open import Agda.Builtin.Bool
open import Agda.Builtin.Float
open import Agda.Builtin.Equality
open import Agda.Builtin.Unit

data ⊥ : Set where

T : Bool → Set
T true  = ⊤
T false = ⊥

cast : {x y : Float} → x ≡ y → T (primFloatEquality x x) → T (primFloatEquality x y)
cast refl t = t

-- Checked with the fast reducer: primFloatACosh is evaluated with acosh.
-- primFloatACosh 1.0 correctly reduces to 0.0:

acosh1fast : primFloatACosh 1.0 ≡ 0.0
acosh1fast = refl

-- The following module, using --no-fast-reduce, should be rejected:

open import Issue8930.SlowReduce using (acosh1slow)

-- Otherwise, we get an inconsistency with --fast-reduce

bot : ⊥
bot = cast acosh1slow tt

-- Expected error:
-- Issue8930/SlowReduce.agda:...: error: [UnequalTerms]
-- The terms
--   0.0
-- and
--   1.5430806348152437
-- are not equal at type Float
-- when checking that the expression refl has type
-- primFloatACosh 1.0 ≡ 1.5430806348152437
