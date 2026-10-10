-- Andreas, 2026-10-10, a regression introduced by PR #8795
-- that broke TypeTopology.
--
-- Non-abstract (non-opaque) metas could no longer be solved
-- from an abstract (opaque) block, not even if the solution
-- does not depend on any abstract (opaque) definition.


postulate
  A : Set
  a : A
  P : A → Set
  p : (x : A) → P x

-- The metas in the type of the helper I need to be solved
-- from the abstract (opaque) block.

test-abstract : P a
test-abstract = t
  where
  I = p _
  abstract
    t : P a
    t = I

test-opaque : P a
test-opaque = t
  where
  I = p _
  opaque
    t : P a
    t = I

-- Shape of the original TypeTopology code:
-- the meta in the type of the helper is eta-expanded
-- and its fields are solved from the abstract block.
-- This is shrunk to the following form:

record R : Set where
  field
    f : A
    g : P f

postulate
  F     : R → Set
  lemma : (x : R) → F x

module _ (r : R) where

  test-record : F r
  test-record = t
    where
    I = lemma _
    abstract
      t : F r
      t = I
