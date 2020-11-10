
open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Builtin.Reflection
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality

pattern vArg x = arg (arg-info visible relevant) x
pattern hArg x = arg (arg-info hidden  relevant) x

constClause : Clause
constClause = clause
             (("A" , hArg (agda-sort (lit 0))) ∷ ("B" , hArg (agda-sort (lit 0))) ∷
              ("x" , vArg (var 1 [])) ∷ ("y" , vArg (var 1 [])) ∷ [])
             (vArg (var 1) ∷ vArg (var 0) ∷ [])
             (var 1 [])

      -- vvv flipped
const : {B A : Set} → A → B → A
unquoteDef const = defineFun const (constClause ∷ [])
-- A != B
-- when checking that all occurrences of pattern variable x have the
-- same type
