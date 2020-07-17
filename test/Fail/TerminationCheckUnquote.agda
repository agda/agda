-- Check that unquoted functions are termination checked.
module _ where

open import Common.Prelude hiding (_>>=_)
open import Common.Reflection
open import Common.Equality

`⊥ : Type
`⊥ = def (quote ⊥) []

⊥-elim : ∀ {a} {A : Set a} → ⊥ → A
⊥-elim ()

{-
Generate
  cheat : ⊥
  cheat = cheat
-}
makeLoop : TC Term
makeLoop =
  freshName "cheat" >>= λ cheat →
  declareDef (vArg cheat) `⊥ >>= λ _ →
  defineFun cheat (clause [] [] (def cheat []) ∷ []) >>= λ _ →
  returnTC (def cheat [])

macro
  magic : Tactic
  magic hole =
    makeLoop >>= λ loop →
    unify hole (def (quote ⊥-elim) (vArg loop ∷ []))

postulate
  ComplexityClass : Set
  P NP : ComplexityClass

thm : P ≡ NP → ⊥
thm = magic
