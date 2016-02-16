
open import Common.Prelude
open import Common.Reflection

id : Nat → Nat
id x = x

-- Used to give error:
-- unquote must be applied to a term
-- when checking that the expression unquote has type _3 x
i : Nat → Nat
i x = unquote (give (def (quote id) [])) x
