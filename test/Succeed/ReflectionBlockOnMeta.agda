
module _ where

open import Common.Prelude hiding (_>>=_; _<$>_)
open import Common.Reflection

infixl 8 _<$>_
_<$>_ : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → TC A → TC B
f <$> m = m >>= λ x → returnTC (f x)

macro
  default : Tactic
  default hole =
    inferType hole >>= λ goal →
    reduce goal >>= λ
    { (def (quote Nat) []) → unify hole (lit (nat 42))
    ; (def (quote Bool) []) → unify hole (con (quote false) [])
    ; (meta x _) → catchTC (blockOnMeta x) (typeError (strErr "impossible" ∷ []))
                                            -- check that the block isn't caught
    ; _ → typeError (strErr "No default" ∷ [])
    }

aNat : Nat
aNat = default

aBool : Bool
aBool = default

alsoNat : Nat

soonNat : _
soonNat = default

alsoNat = soonNat
