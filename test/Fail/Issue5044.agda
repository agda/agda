
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

id-ok : {A : Set} → A → A
unquoteDef id-ok = defineFun id-ok (idClause-ok ∷ [])

idClause-fail : Clause
idClause-fail = clause
             (("A" , hArg (agda-sort (lit 0))) ∷ ("x" , vArg (var 0 [])) ∷  ("y" , vArg (var 1 []))  ∷ [])
             ({-hArg (var 1) ∷-} vArg (var 0) ∷ [])  -- "A" (var 2) and "x" (var 1) not bound here
             (var 0 [])

id-fail : {A : Set} → A → A → A
unquoteDef id-fail = defineFun id-fail (idClause-fail ∷ [])

-- WAS: Panic: unbound variable A (id: 191@9559440724209987811)
-- when checking that the expression A has type _7

-- error: [MissingBindingsForTelescopeVariables]
-- Missing bindings for telescope variables: A x
-- All variables in the clause telescope must be bound in the left-hand side.
