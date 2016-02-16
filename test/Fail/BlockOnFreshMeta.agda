
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
  shouldNotCrash : Tactic
  shouldNotCrash hole = blockOnFresh

-- Should leave some yellow and a constraint 'unquote shouldNotCrash : Nat'
n : Nat
n = shouldNotCrash
