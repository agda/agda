-- Andreas, 2026-10-19, issue #8851
-- A declaration rolled back by runSpeculative
-- does not need to be defined.

module Issue8851-speculative where

open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Agda.Builtin.Sigma
open import Agda.Builtin.List

_>>=_ = bindTC

unquoteDecl =
  freshName "tmp" >>= λ tmp →
  runSpeculative (
    declareDef (arg (arg-info visible (modality relevant quantity-ω)) tmp) (def (quote ⊤) []) >>= λ _ →
    returnTC (tt , false))
