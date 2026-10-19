-- Andreas, 2026-02-27, issue #2591, fixed by PR #8079
-- Scope error should be reported instead of parse error.

mutual

  infixl 6 _+_

  data D : Set where
    _+_ : (x y : D) → D
    bla : ∀ x y z → E x y z  → D

  postulate
    f : ∀ x y z → _+_ x y ≡ z            -- expect scope error here

  data E (x y : D) : D → Set where
    e : ∀ z → (f : _+_ x y ≡ z) → E x y z

-- Error WAS: Could not parse application `_+_ x y`

-- Expected error: [NotInScope]
-- Not in scope:
--   _+_ at (postulate f)
-- when scope checking _+_
