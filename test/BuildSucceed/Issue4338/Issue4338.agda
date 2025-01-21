-- Andreas, 2025-01-21, issue #4338
-- Some random code requiring the library flag --sized-types.

open import Agda.Primitive
open import Agda.Builtin.Size

record U (i : Size) : Set where
  coinductive
  field force : {j : Size< i} → U j
open U

inhabit : ∀{i} → U i
inhabit .force {j} = inhabit {_}

-- Should succeed.
