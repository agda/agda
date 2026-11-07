{-# OPTIONS --double-check #-}

module Issue434 where

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

record Family : Set₁ where
  constructor family
  field A : Set

  H : Bool → Set
  H true = A
  H false = A → A

  private
    identity : A → A
    identity a = local a
      where
      local : A → A
      local x = x

  iterate : Nat → (A → A) → A → A
  iterate zero f a = a
  iterate (suc n) f a = iterate n f (f a)

  module Maps (f : A → A) where
    twice : A → A
    twice a = f (f a)

  field x : (b : Bool) → H b

  chosen : A
  chosen = identity (x true)

example : Family
example = family Nat (λ { true → zero ; false → suc })

test : Family.chosen example ≡ zero
test = refl

module Copy = Family

testCopy : Copy.chosen example ≡ zero
testCopy = refl

testNested : Family.Maps.twice example suc zero ≡ suc (suc zero)
testNested = refl

-- A local datatype is shared by the constructor telescope and public copies.
record WithData : Set₁ where
  constructor withData
  field A : Set

  data D : Set where
    wrap : A → D

  field payload : D

testData : (r : WithData) → WithData.D r
testData r = WithData.payload r

-- Changing a later field does not change the identity of the earlier datatype.
testDataIdentity : (r : WithData) (d e : WithData.D r) →
  WithData.D (withData (WithData.A r) d) →
  WithData.D (withData (WithData.A r) e)
testDataIdentity r d e x = x
