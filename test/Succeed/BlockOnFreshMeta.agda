
module _ where

open import Common.Prelude hiding (_>>=_)
open import Common.Reflection
open import Common.Equality

infix 0 case_of_
case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = f x

blockOnFresh : TC ⊤
blockOnFresh =
  checkType unknown unknown >>= λ
  { (meta m _) → blockOnMeta m
  ; _ → typeError (strErr "impossible" ∷ []) }

macro
  weirdButShouldWork : Tactic
  weirdButShouldWork hole =
    inferType hole >>= λ goal →
    reduce goal >>= λ goal →
    case goal of λ
    { (meta _ _) → blockOnFresh
    ; _ → unify hole (lit (nat 42))
    }

-- When the goal is a meta the tactic will block on a different, fresh, meta.
-- That's silly, but should still work. Once the goal is resolved the tactic
-- doesn't block any more so everything should be fine.
thing  : _
solves : Nat
thing  = weirdButShouldWork
solves = thing

check : thing ≡ 42
check = refl
