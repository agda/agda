{-# OPTIONS --prop --safe #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat hiding (_<_)

data _<_ : Nat → Nat → Set where
  zero-< : ∀ {n} → zero < suc n
  suc-<  : ∀ {m n} → m < n → suc m < suc n

record Acc (a : Nat) : Prop where
  inductive
  pattern
  constructor acc
  field acc< : (∀ b → b < a → Acc b)

open Acc

AccRect : ∀ {P : Nat → Set} → (∀ a → (∀ b → b < a → Acc b) → (∀ b → b < a → P b) → P a) → ∀ a → Acc a → P a
AccRect f a (acc p) = f a p (λ b b<a → AccRect f b (p b b<a))

AccRectProp : ∀ {P : Nat → Prop} → (∀ a → (∀ b → b < a → Acc b) → (∀ b → b < a → P b) → P a) → ∀ a → Acc a → P a
AccRectProp f a (acc p) = f a p (λ b b<a → AccRectProp f b (p b b<a))

AccInv : ∀ a → Acc a → ∀ b → b < a → Acc b
AccInv = AccRectProp (λ _ p _ → p)

example : ∀ {P : Nat → Set} → (f : ∀ a → (∀ b → b < a → P b) → P a) → ∀ a → (access : Acc a) →
  AccRect {P} (λ a _ r → f a r) a access ≡ f a (λ b b<a → AccRect {P} (λ a _ r → f a r) b (AccInv a access b b<a))
example f a access = ?
