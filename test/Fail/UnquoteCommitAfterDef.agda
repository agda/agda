open import Common.Prelude hiding (_>>=_)
open import Common.Reflection

_ : Nat
_ = unquote λ _ →
  freshName "aux" >>= λ aux →
  declareDef (vArg aux) (def (quote ⊥) []) >>= λ _ →
  commitTC
