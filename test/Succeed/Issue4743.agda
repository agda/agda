{-# OPTIONS --guardedness --erasure #-}

open import Agda.Builtin.Bool
open import Agda.Builtin.Coinduction
open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit

-- An example from the changelog.

@0 f : @0 Bool → Bool
f = λ where
  true  → false
  false → true

-- Macros that are run in type signatures do not automatically create
-- erased definitions.

macro

  Unify-with-new-postulate : Term → TC ⊤
  Unify-with-new-postulate goal =
    bindTC (freshName "A") λ name →
    bindTC (declarePostulate
              (arg (arg-info visible (modality relevant quantity-ω))
                   name)
              (agda-sort (lit 0))) λ _ →
    unify goal (def name [])

mutual

  B : Set
  B = _

  B≡ : B ≡ Unify-with-new-postulate
  B≡ = refl

-- An example involving a generalisable variable. This example failed
-- for an earlier implementation in which the pattern-matching lambda
-- was treated as non-erased but the constants added by
-- Agda.TypeChecking.Generalize.createGenRecordType were treated as
-- erased.

private variable
  A : Set

data Unit : Set where
  unit : Unit

postulate
  P : Set → (Unit → Unit) → Set
  g : (A : Set) (h : Unit → Unit) → P A h

_ : P A λ { unit → unit }
_ = g _ _

-- An example involving the "sharp" function.

mutual

  x : ∞ Bool
  x = _

  _ : x ≡ ♯ true
  _ = refl

-- An example involving an absurd lambda.

data ⊥ : Set where

mutual

  h : ⊥ → Set
  h = _

  _ : h ≡ λ ()
  _ = refl

-- An example involving an erased definition with a where clause and a
-- module application (see also test/Fail/Issue5410-1.agda and
-- test/Fail/Issue5410-2.agda).

module M (_ : Set) where

@0 C : @0 Set → Set
C A = Bool
  module N where
    module O = M A
