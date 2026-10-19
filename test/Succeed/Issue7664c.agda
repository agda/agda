-- Andreas, 2026-09-25, issue #7664.
-- The parameter check must not fire when the module instantiation
-- fixes nothing, also not when it permutes the parameters.

module Issue7664c where

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool

data Access : Set where
  pub priv : Access

module M (A : Set) (a : Access) (B : Set) where
  data D : Set where
    c : A → B → D

-- Parameters swapped, nothing fixed.
module N1 (Y2 : Set) (a : Access) (Y1 : Set) = M Y1 a Y2

f1 : M.D Nat priv Bool → Nat
f1 (N1.c x y) = x

-- Parameters swapped, middle one fixed to `pub`, and we split at `pub`.
module N2 (Y2 : Set) (Y1 : Set) = M Y1 pub Y2

f2 : M.D Nat pub Bool → Nat
f2 (N2.c x y) = x

-- Chain of copies, permuted at each level, split at `pub`.
module N3 (Z1 : Set) (Z2 : Set) = N2 Z2 Z1

f3 : M.D Nat pub Bool → Nat
f3 (N3.c x y) = x
