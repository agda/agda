-- Andreas, 2019-03-27
-- Do not run checkIApplyConfluence unless --cubical

-- The following verbosity options triggers a crash
-- in case checkIApplyConfluence_ runs.

-- {-# OPTIONS --cubical #-}  -- Trigges the crash.

{-# OPTIONS -v tc.cover.iapply.confluence.crash:666 #-}  -- Activate crashing program point.

open import Agda.Builtin.Nat

-- A harmless definition.

id : Nat → Nat
id zero    = zero
id (suc x) = suc (id x)

-- Should succeed.
