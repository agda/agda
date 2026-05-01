-- Andreas, 2026-04-30, issue #6770, reported by Orestis Melkonian

open import Agda.Builtin.Equality
postulate
  X Y : Set
  f : X → Y
  P : Y → Set
variable
  x : X
module M (x : X) where
  y = f x
-- ** these all work
module _ {x} (open M x) where
  postulate _ : P y
postulate
  _ : let open M x in P y
  _ : (open M x) → P y
-- ** this raises unexpected error on `y`, suggesting that it has not been properly instantiated
module _ (open M x) where
  postulate _ : P y

-- Should succeed
