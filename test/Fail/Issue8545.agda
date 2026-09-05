-- Andreas, 2026-09-02, issue #8545.
--
-- The parameters fixed by a partial module instantiation have to
-- agree with the parameters of the data type we are splitting on,
-- even when the constructor is reached via nested module copies.

module Issue8545 where

record TC : Set where

instance
  tc : TC
  tc = record {}

postulate A B : Set

module M (X : Set) ⦃ _ : TC ⦄ where
  data D : Set where
    c : X → D

record R : Set₁ where
  field dummy : Set
  open M A public

r : R
r = record { dummy = A }
open R r

-- Should be rejected: `c` constructs `M.D A`, not `M.D B`.

f : M.D B → Set₁
f (c k) = Set
