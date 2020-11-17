
open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Builtin.Reflection
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality

pattern vArg x = arg (arg-info visible relevant) x
pattern hArg x = arg (arg-info hidden  relevant) x

idClause-ok : Clause
idClause-ok = clause
             (("A" , hArg (agda-sort (lit 0))) ∷ ("x" , vArg (var 0 [])) ∷ [])
             (hArg (var 1) ∷ vArg (var 0) ∷ [])
             (var 0 [])

id-ok : {A : Set} → A → A
unquoteDef id-ok = defineFun id-ok (idClause-ok ∷ [])

idClause-fail : Clause
idClause-fail = clause
             (("A" , hArg (agda-sort (lit 0))) ∷ ("x" , vArg (var 0 [])) ∷ [])
             ({-hArg (var 1) ∷-} vArg (var 0) ∷ [])
             (var 0 [])

id-fail : {A : Set} → A → A
unquoteDef id-fail = defineFun id-fail (idClause-fail ∷ [])
-- Panic: unbound variable A (id: 191@9559440724209987811)
-- when checking that the expression A has type _7
