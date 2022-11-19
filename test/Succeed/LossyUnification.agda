{-# OPTIONS --experimental-lossy-unification #-} -- sic!
  -- Keep the deprecated option name for the sake of #6337

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

-- Lossy unification solves these metas.
test : 3 + 4 ≡ _ + _
test = refl

-- Expected warning:
-- Option --experimental-lossy-unification is deprecated, please use --lossy-unification instead
