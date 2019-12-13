module Issue3879 where

open import Issue3879.Fin    using (Fin ; zero ; suc)
open import Agda.Builtin.Nat using (Nat ; zero ; suc)

foo : Nat → Nat → Nat
foo zero m = {!!}
foo (suc n) m = {!!}

-- WAS: case-splitting on m produces Issue3879.Fin.0F patterns
-- WANT: unqualified 0F is not in scope: do not resugar!
