------------------------------------------------------------------------
-- Operations on nullary relations (like negation and decidability)
------------------------------------------------------------------------

-- Some operations on/properties of nullary relations, i.e. sets.

module Relation.Nullary where

open import Data.Empty
open import Data.Product
import Relation.Binary.PropositionalEquality as PropEq
open PropEq using (_≡_; sym; cong)
open PropEq.≡-Reasoning
import Relation.Nullary.Core as Core

------------------------------------------------------------------------
-- Negation

open Core public using (¬_)

------------------------------------------------------------------------
-- Equivalence

infix 3 _⇔_

_⇔_ : Set → Set → Set
P ⇔ Q = (P → Q) × (Q → P)

------------------------------------------------------------------------
-- Decidable relations

open Core public using (Dec; yes; no)

------------------------------------------------------------------------
-- Injections

-- I cannot be bothered to generalise to an arbitrary setoid.

Injective : ∀ {A B} → (A → B) → Set
Injective f = ∀ {x y} → f x ≡ f y → x ≡ y

_LeftInverseOf_ : ∀ {A B} → (B → A) → (A → B) → Set
f LeftInverseOf g = ∀ x → f (g x) ≡ x

record Injection A B : Set where
  field
    to        : A → B
    injective : Injective to

record LeftInverse A B : Set where
  field
    to           : A → B
    from         : B → A
    left-inverse : from LeftInverseOf to

  injective : Injective to
  injective {x} {y} eq = begin
    x            ≡⟨ sym (left-inverse x)  ⟩
    from (to x)  ≡⟨ cong from eq ⟩
    from (to y)  ≡⟨ left-inverse y ⟩
    y            ∎

  injection : Injection A B
  injection = record { to = to; injective = injective }
