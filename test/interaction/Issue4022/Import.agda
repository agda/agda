module Issue4022.Import where

open import Agda.Builtin.Nat

Binary : Set
Binary = Nat → Nat → Nat

-- Search should be able to find `plus` if:
-- * either we do not normalise the type and look for `Binary`
-- * or we do normalise the type and look for `Nat`

plus : Binary
plus = _+_
