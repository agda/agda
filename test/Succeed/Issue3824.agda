-- Andreas, 2019-05-30, issue #3824:
-- Named where module should be in scope even if defined under a rewrite.

open import Agda.Builtin.Equality

postulate
  A   : Set
  a b : A
  a≡b : a ≡ b
  P   : A → Set

cast : P a → P b
cast p rewrite a≡b = q
  module M where
    q = p

test : P b → P b
test = M.q

-- ERROR WAS: M.q not in scope.

module Test = M

-- ERROR WAS: M not in scope.

-- Should succeed.
