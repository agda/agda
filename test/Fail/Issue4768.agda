-- Andreas, 2020-06-21, issue #4768
-- Problem was: @0 appearing in "Not a finite domain" message.

open import Agda.Builtin.Bool
open import Agda.Primitive.Cubical

f : (i : I) → IsOne i → Set
f i (i0 = i1) = Bool

-- EXPECTED:
-- Not a finite domain: IsOne i
-- when checking that the pattern (i0 = i1) has type IsOne i
