-- Andreas, 2025-08-08, transient internal error during work on #7001.

{-# OPTIONS --erasure #-}

-- {-# OPTIONS -v tc.term.lambda:30 #-}

open import Agda.Builtin.Equality

postulate
  A : Set

@0 spec : A → A
spec n  = n

impl    : A → A
impl n  = n

proof   : ∀ n → spec n ≡ impl n
proof n = λ _ → n

-- Should give type error: λ without function type.
-- During work on #7001, this produced an internal error at some point.

-- Expected error: [UnequalTerms]
-- (z : _10) → A !=< spec n ≡ impl n
-- when checking that the expression λ _ → n has type spec n ≡ impl n
