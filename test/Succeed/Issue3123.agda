-- Andreas, 2025-11-12, issue #3123, reported by Ulf Norell.
-- Projection-like functions triggered an internal error
-- when applied to module parameters.

-- {-# OPTIONS --no-projection-like #-} -- turns off internal error
-- {-# OPTIONS -v tc.rec:20 #-}
-- {-# OPTIONS -v tc.term:20 #-}
-- {-# OPTIONS -v tc.term.def:30 #-}
-- {-# OPTIONS -v tc.sig.inst:30 #-}
-- {-# OPTIONS -v tc.irr:50 #-}
-- {-# OPTIONS -v tc.sig.param:90 #-}
-- {-# OPTIONS -v tc.signature:20 #-}
-- {-# OPTIONS -v tc.signature:60 #-}  -- enlightening "adding constant ..._.Carrier"
-- {-# OPTIONS -v tc.signature:80 #-}
-- {-# OPTIONS -v tc.proj.like:30 #-}  -- enlightening
-- {-# OPTIONS -v tc.mod.apply:80 #-}  -- origin of "addConstant"

record Setoid (A : Set) : Set1 where
  field
    Carrier : Set

module M A (setoid : Setoid A) (TriggerError : Set) where
  open Setoid setoid
  -- This creates a projection-like function
  --
  --   Carrier : (A : Set) → Setoid A → Set → Set
  --
  -- with the second argument as the principal argument.
  -- The previous implementation assumed that instantiation
  -- beyond the principal argument would not be possible.
  -- So the instantiation to [A, setoid, TriggerError]
  -- crashed.
  postulate
    elem : Carrier  -- Checking this type crashed.

-- This triggered an internal error (a spurious __IMPOSSIBLE__).
-- Should succeed.
