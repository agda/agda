
module _ where

open import Common.Prelude
open import Common.Reflection
open import Common.Equality

record Foo (A : Set) : Set where
  field
    foo : A → Nat

open Foo {{...}}

instance
  FooNat : Foo Nat
  foo {{FooNat}} n = n

  FooBool : Foo Bool
  foo {{FooBool}} true  = 1
  foo {{FooBool}} false = 0

macro
  do-foo : ∀ {A} {{_ : Foo A}} → A → Tactic
  do-foo x = give (lit (nat (foo x)))

test₁ : do-foo 5 ≡ 5
test₁ = refl

test₂ : do-foo false ≡ 0
test₂ = refl

macro
  lastHidden : {n : Nat} → Tactic
  lastHidden {n} = give (lit (nat n))

test₃ : lastHidden {4} ≡ 4
test₃ = refl

macro
  hiddenTerm : {a : Term} → Tactic
  hiddenTerm {a} = give a

test₄ : hiddenTerm {4} ≡ 4
test₄ = refl
