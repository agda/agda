
module _ where

open import Agda.Builtin.Equality
open import Agda.Builtin.Bool
open import Agda.Builtin.Unit
open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.Reflection renaming (returnTC to return; bindTC to _>>=_)

_>>_ : {A B : Set} → TC A → TC B → TC B
m >> m' = m >>= λ _ → m'

macro
  solve : Nat → Term → TC ⊤
  solve blocker hole = do
    unify hole (lam visible (abs "x" (var 0 [])))
    meta x _ ← withNormalisation true (quoteTC blocker)
      where _ → return _
    blockOnMeta x

mutual
  blocker : Nat
  blocker = _

  bug : Bool
  bug = (solve blocker) true

  unblock : blocker ≡ 0
  unblock = refl
