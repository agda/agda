{-# OPTIONS --large-indices #-}
module _ where

open import Common.Prelude hiding (_>>=_)
open import Common.Reflection
open import Agda.Builtin.Sigma

infix -100 This:_ this:_
data This:_ {a} {A : Set a} : A → Set where
  this:_ : ∀ x → This: x

macro
  runT : Tactic → Tactic
  runT m = m

  evalT : ∀ {a} {A : Set a} → TC A → Tactic
  evalT m hole = m >>= quoteTC >>= unify hole

-- The context on the rhs of each of the two functions below is the same, a single String

Γ : Telescope
Γ = ("s" , vArg (def (quote String) [])) ∷ []

context-Γ₀ : String → This: Γ
context-Γ₀ s = this: evalT getContext

module _ (S : String) where
  Γ' : Telescope
  Γ' = ("S" , vArg (def (quote String) [])) ∷ []

  context-Γ₁ : This: Γ'
  context-Γ₁ = this: evalT getContext

downMap : {A : Set} → (Nat → A) → Nat → List A
downMap f zero    = []
downMap f (suc n) = f n ∷ downMap f n

f-type : Term
f-type = def (quote String) []

f-tel : Nat → List (Σ String λ _ → Arg Type)
f-tel n = downMap (λ _ → "_" , vArg unknown) n

f-pats : Nat → List (Arg Pattern)
f-pats n = downMap (λ x → vArg (var x)) n

f-term : Nat → Term
f-term n = var n []

defineFresh : Nat → Nat → TC QName
defineFresh #pats #term =
  freshName "f" >>= λ f →
  define (vArg f) (funDef f-type (clause (f-tel #pats) (f-pats #pats) (f-term #term) ∷ [])) >>= λ _ →
  returnTC f

freshFun : Nat → Nat → TC Bool
freshFun #pats #term =
  catchTC (defineFresh #pats #term >>= λ _ → returnTC true)
          (returnTC false)

-- Check that the pattern list must be of length 0
-- and the context features 1 available variable.

define-Γ₀-0-0 : String → This: true
define-Γ₀-0-0 s = this: evalT (freshFun 0 0)

define-Γ₀-1-0 : String → This: false
define-Γ₀-1-0 s = this: evalT (freshFun 1 0)

define-Γ₀-1-1 : String → This: false
define-Γ₀-1-1 s = this: evalT (freshFun 0 1)

module _ (S : String) where
  define-Γ₁-0-0 : This: true
  define-Γ₁-0-0 = this: evalT (freshFun 0 0)

  define-Γ₁-0-1 : This: false
  define-Γ₁-0-1 = this: evalT (freshFun 0 1)

  define-Γ₁-1-0 : This: false
  define-Γ₁-1-0 = this: evalT (freshFun 1 0)

f₀ : String → String
f₀ s = runT λ hole → defineFresh 0 0 >>= λ f → unify hole (def f [])

f₁ : String → String
f₁ = λ s → runT λ hole → defineFresh 0 0 >>= λ f → unify hole (def f [])

f₂ : String → String
f₂ s = runT λ hole → defineFresh 0 0 >>= λ f → unify hole (def f [])
  where x = 0
