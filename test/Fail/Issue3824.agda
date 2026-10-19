-- Andreas, 2019-05-30, issue #3824:
-- Named where module should be in scope even if defined under a rewrite.

-- Andreas, 2026-09-06, issue #8698:
-- Named where modules under `rewrite` are unsound, because the
-- with-abstraction can change the types of the module parameters they
-- inherit.  They are disallowed since Agda 2.9.0, so this test now fails.

open import Agda.Builtin.Equality

postulate
  A   : Set
  a b : A
  a≡b : a ≡ b
  P   : A → Set

cast : P a → P b
cast p rewrite a≡b = q
  module M where  -- rejected here now
    q = p

-- We no longer reach this (#8698):
test : P b → P b
test = M.q       -- WAS before #3824: not in scope

module Test = M  -- ditto
