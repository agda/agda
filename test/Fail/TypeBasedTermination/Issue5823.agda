{-# OPTIONS --no-syntax-based-termination #-}  -- OR: no-syntax-based...
{-# OPTIONS --type-based-termination #-}

-- Andreas, 2024-05-17, issue #7284, original issue #5823, reported by oisdk
-- It is possible again (with TBT) to make the check for singleton records loop.

module TypeBasedTermination.Issue5823 where

open import Agda.Primitive
open import Agda.Builtin.Equality

isProp : ∀{a} (A : Set a) → Set a
isProp A = ∀ (x y : A) → x ≡ y

cong : ∀{a b} {A : Set a} {B : Set b} (f : A → B) {x y : A} (eq : x ≡ y) → f x ≡ f y
cong f refl = refl

postulate
  funExt : ∀{a b}{A : Set a} {B : (x : A) → Set b} {f g : (x : A) → B x} → (∀ (x : A) → f x ≡ g x) → f ≡ g

record Acc {a} {A : Set a} {r} (R : A → A → Set r) (x : A) : Set (a ⊔ r) where
  inductive; eta-equality
  constructor acc
  field step : ∀ y → R y x → Acc R y
open Acc public

-- Naively testing Acc R x for being a singleton will infinitely unfold its definition.
-- We need to keep track of which record types we already unfolded!

-- Don't do this at home: Agda LOOPS!
-- isPropAcc : ∀ {a r} {A : Set a} {R : A → A → Set r} {x : A} → isProp (Acc R x)
-- isPropAcc (acc x) (acc y) = cong acc (funExt λ n → funExt λ p → isPropAcc (x n p) (y n p))

-- -- Loops when trying determine whether Acc is a singleton type.
