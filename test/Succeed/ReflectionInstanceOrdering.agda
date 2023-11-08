module ReflectionInstanceOrdering where

open import Agda.Builtin.Reflection
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat

postulate
  F : Set → Set
  G : Set → Set
  instance
    F-nat : ∀ {b} → F (Nat → b)
    F-fn  : ∀ {a b} → ⦃ _ : G b ⦄ → F (a → b)
    F-nat-nat : F (Nat → Nat)

_>>=_ : ∀ {a b} {A : Set a} {B : Set b} → TC A → (A → TC B) → TC B
_>>=_ = bindTC

pattern argN x = arg (arg-info visible (modality relevant quantity-ω)) x

list : List Term → Term
list []              = con (quote []) []
list (def x [] ∷ xs) = con (quote _∷_) (argN (lit (name x)) ∷ argN (list xs) ∷ [])
list (_ ∷ _)         = con (quote zero) []

instances : TC Term
instances = runSpeculative do
  meta mv _ ← checkType unknown (def (quote F) (argN unknown ∷ []))
    where _ → typeError []
  xs ← getInstances mv
  returnTC (list xs , false)

names : List Name
names = unquote λ goal → do
  xs ← instances
  unify goal xs

_ : names ≡ quote F-nat-nat ∷ quote F-nat ∷ quote F-fn ∷ []
_ = refl
