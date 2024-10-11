module Issue1389 where

open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Builtin.Reflection
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality

pattern default-modality = modality relevant quantity-ω
pattern vArg x = arg (arg-info visible default-modality) x
pattern hArg x = arg (arg-info hidden  default-modality) x

idClause-ok : Clause
idClause-ok = clause
             (("A" , hArg (agda-sort (lit 0))) ∷ ("x" , vArg (var 0 [])) ∷ [])
             (hArg (var 1) ∷ vArg (var 0) ∷ [])
             (var 0 [])

unquoteDef id-ok = defineFun id-ok (idClause-ok ∷ [])
