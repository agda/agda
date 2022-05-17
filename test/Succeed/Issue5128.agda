
open import Agda.Builtin.Unit
open import Agda.Builtin.Sigma
open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Agda.Builtin.Reflection renaming (bindTC to infixl 4 _>>=_)

macro
  quoteDef : Name → Term → TC ⊤
  quoteDef f hole = (getDefinition f >>= quoteTC) >>= unify hole

postulate
  A : Set
  B : A → Set

-- foo is projection-like
foo : (x : A) → B x → B x
foo x y = y

pattern vArg x = arg (arg-info visible (modality relevant quantity-ω)) x

test : quoteDef foo ≡
  function
    (clause
     (("x" , vArg (def (quote A) [])) ∷
      ("y" , vArg (def (quote B) (vArg (var 0 []) ∷ [])))
      ∷ [])
     (vArg (var 1) ∷ vArg (var 0) ∷ [])
     (var 0 [])
     ∷ [])
test = refl
