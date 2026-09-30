-- Andreas, 2017-03-21, issue #2466

-- The unifier should not turn user-written variable patterns into
-- dot patterns.

-- {-# OPTIONS -v reify.implicit:100 -v interaction.case:100 #-}
-- {-# OPTIONS -v tc.lhs.unify:40 #-}

postulate
  A B : Set

module Explicit where

  data D : A → B → Set where
    c : ∀ p {p'} x → D p' x → D p x

  test : ∀ p x → D p x → D p x
  test .p _ (c p x pp) = {!p'!}
    where
    y = x

  -- Expected: test .p _ (c p {p'} x pp) = ?

module Implicit where

  data D : A → B → Set where
    c : ∀ {p p' x} → D p' x → D p x

  test : ∀ p {x} → D p x → D p x
  test .p (c {p} {x = x} pp) = {!p'!}
    where
    y = x

  -- Expected: test .p (c {p} {p'} {x = x} pp) = ?
