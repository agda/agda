
open import Agda.Builtin.Reflection
open import Agda.Builtin.String
open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.Unit
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma

data Wrap (A : Set) : Set where
  [_] : A → Wrap A

macro
  give : Wrap Term → Term → TC ⊤
  give [ t ] hole = unify hole t

pattern vArg x = arg (arg-info visible relevant) x
pattern hArg x = arg (arg-info hidden  relevant) x

-- Naming the variable "_" doesn't affect the deBruijn indices for lambda and pi

`id : Term
`id = lam visible (abs "_" (var 0 []))

`IdType : Term
`IdType = pi (hArg (agda-sort (lit 0))) (abs "_" (pi (vArg (var 0 [])) (abs "_" (var 1 []))))

id : give [ `IdType ]
id = give [ `id ]

id-ok : (λ {A : Set} (x : A) → x) ≡ id
id-ok = refl

-- Underscores should behave the same for clauses as for lambda and pi

idClause : Clause
idClause = clause
             (("_" , vArg unknown) ∷ ("_" , hArg unknown) ∷ [])
             (hArg (var 1) ∷ vArg (var 0) ∷ [])
             (var 0 [])

infixr 4 _>>=_
_>>=_ = bindTC

unquoteDecl id₂ =
  declareDef (vArg id₂) `IdType >>= λ _ →
  defineFun id₂ (idClause ∷ [])

id₂-ok : (λ {A : Set} (x : A) → x) ≡ id₂
id₂-ok = refl
