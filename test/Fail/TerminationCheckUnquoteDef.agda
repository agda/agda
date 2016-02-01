-- Check that unquoted functions are termination checked.
module _ where

open import Common.Prelude hiding (_>>=_)
open import Common.Reflection
open import Common.TC

infixr 1 _>>=_
_>>=_ = bindTC

`⊥ : Type
`⊥ = def (quote ⊥) []

{-
Generate
  aux : ⊥
  aux = aux

  loop : ⊥
  loop = aux
-}
makeLoop : QName → TC ⊤
makeLoop loop =
  freshName "aux" >>= λ aux →
  declareDef (vArg aux) `⊥ >>= λ _ →
  defineFun aux (clause [] (def aux []) ∷ []) >>= λ _ →
  defineFun loop (clause [] (def aux []) ∷ [])

loop : ⊥
unquoteDef loop = makeLoop loop
