module Issue1280 where

open import Common.Prelude
open import Common.Reflection

infixr 5 _∷_

data Vec (A : Set) : Nat → Set where
  [] : Vec A 0
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

test : Vec _ _
test = 0 ∷ []

quoteTest : Term
quoteTest = quoteTerm test

unquoteTest = unquote (give quoteTest)

data Foo (A : Set) : Set where
  foo : Foo A

ok : Foo Nat
ok = unquote (give (quoteTerm (foo {Nat})))

-- This shouldn't type-check. The term `bad` is type-checked because
-- the implicit argument of `foo` is missing when using quoteTerm.
bad : Foo Bool
bad = unquote (give (quoteTerm (foo {Nat})))
