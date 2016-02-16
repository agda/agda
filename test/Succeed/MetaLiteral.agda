
module _ where

open import Common.Prelude hiding (_>>=_)
open import Common.Reflection
open import Common.Equality

macro
  metaLit : Tactic
  metaLit hole =
    checkType unknown (def (quote Nat) []) >>= λ
    { (meta m args) →
      unify hole (lit (meta m)) >>= λ _ →
      unify (meta m args) (lit (nat 42))
    ; _ → typeError (strErr "not a meta" ∷ []) }

  unquoteMeta : Meta → Tactic
  unquoteMeta m = give (meta m [])

m : Meta
m = metaLit

thm : unquoteMeta m ≡ 42
thm = refl
