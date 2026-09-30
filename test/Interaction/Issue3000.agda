
open import Agda.Primitive

Type : (i : Level) → Set (lsuc i)
Type i = Set i

postulate
  T : (i : Level) (A : Type i) → Set

-- Give 'T lzero ?', then give '? → ?'.
-- An internal error has occurred. Please report this as a bug.
-- Location of the error: src/full/Agda/TypeChecking/Rules/Term.hs:178
Bug : Set
Bug = {!T lzero ?!}

-- Now: Failed to give (? → ?)
-- Ideally, this should succeed.
