-- Andreas, 2024-10-11 trigger error Unquote.MissingDeclaration

open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Builtin.Reflection
open import Agda.Builtin.Sigma

pattern default-modality = modality relevant quantity-ω
pattern vArg x = arg (arg-info visible default-modality) x
pattern hArg x = arg (arg-info hidden  default-modality) x

idClause-ok : Clause
idClause-ok = clause
             (("A" , hArg (agda-sort (lit 0))) ∷ ("x" , vArg (var 0 [])) ∷ [])
             (hArg (var 1) ∷ vArg (var 0) ∷ [])
             (var 0 [])

unquoteDecl data id-ok = defineFun id-ok (idClause-ok ∷ [])

-- error: [Unquote.MissingDeclaration]
-- Missing declaration for id-ok
