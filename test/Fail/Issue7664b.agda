-- Andreas, 2026-09-25, issue #7664.
-- The parameter fixed by the module instantiation has to be checked
-- also when the copies permute the parameters of the original,
-- and through a chain of copies.

module Issue7664b where

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool

data Access : Set where
  pub priv : Access

module M (A : Set) (a : Access) (B : Set) where
  data D : Set where
    c : A → B → D

-- N.D Y2 Y1 = M.D Y1 pub Y2,  O.D Z1 Z2 = N.D Z2 Z1 = M.D Z1 pub Z2
module N (Y2 : Set) (Y1 : Set) = M Y1 pub Y2
module O (Z1 : Set) (Z2 : Set) = N Z2 Z1

-- Should be rejected: O.c only constructs `M.D _ pub _`.
f : M.D Nat priv Bool → Nat
f (O.c x y) = x

-- Expected error: [UnequalTerms]
-- The terms
--   pub
-- and
--   priv
-- are not equal at type Access
-- when checking that the pattern O.c x y has type M.D Nat priv Bool
