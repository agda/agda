-- Andreas, 2018-10-17, re issue #2757
--
-- Matching on runtime-irrelevant arguments is fine
-- as long as it produces only one branch.

{-# OPTIONS --erasure #-}

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

-- Matching on empty types can be erased.

data ⊥ : Set where

⊥-elim : ∀{A : Set} → @0 ⊥ → A
⊥-elim ()

-- Accessibility.

data Acc {A : Set} (R : A → A → Set) (x : A) : Set where
  acc : (∀{y} (y<x : R y x) → Acc R y) → Acc R x

-- Accessibility proofs can be erased.

wfrec : {A : Set} (R : A → A → Set) {P : A → Set}
  → (∀{x} → (∀{y} (@0 y<x : R y x) → P y) → P x)
  → ∀{x} (@0 ax : Acc R x) → P x
wfrec R f (acc h) = f λ y<x → wfrec R f (h y<x)

-- Non-branching matches can be erased.

diag : ∀(@0 x) (y : Bool) (@0 eq : x ≡ y) → Bool
diag false false refl = false
diag true  y     refl = y

diag' : ∀ x (@0 y : Bool) (@0 eq : x ≡ y) → Bool
diag' false  false refl = false
diag' x@true y     refl = x

-- Also for literals.

nonBranchLit : ∀ (@0 x) (eq : x ≡ 0) → Set
nonBranchLit 0 refl = Nat

-- The attribute syntax collides lexically with the as-pattern syntax.

userConfusingClashOfAttributesAndAsPatterns : ∀ (@0 x) (eq : x ≡ 0) → Set
userConfusingClashOfAttributesAndAsPatterns (x @0) refl = Nat
