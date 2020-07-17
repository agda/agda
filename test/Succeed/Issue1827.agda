
open import Common.Prelude hiding (_>>=_)
open import Common.Reflection
open import Common.Equality

set₀ = sort (lit 0)
set! = sort unknown

-- Definitions added by tactics always use the original context, and thus are not
-- affected by inContext and extendContext. The reason for this is that they are added
-- to the module of the macro call, so they need to live in the context of that module
-- or things break.

freshFun : Type → List Clause → Tactic
freshFun t cs hole =
  freshName "fresh" >>= λ n →
  inContext [] (define (vArg n) (funDef t cs)) >>= λ _ →
  unify hole (def n [])

macro
  ack : Tactic
  ack = freshFun set! (clause [] [] set₀ ∷ [])

  theA : Tactic
  theA = freshFun set₀ (clause [] [] (var 0 []) ∷ [])

module Foo (A : Set) where
  foo : Set
  foo = theA

  bar : Set₁
  bar = ack

check : {A : Set} → Foo.foo A ≡ A
check = refl
