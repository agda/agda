{-# OPTIONS --rewriting --confluence-check #-}

open import Agda.Primitive

postulate
  _↦_ : ∀{i j}{A : Set i}{B : Set j} → A → B → Set (i ⊔ j)

{-# BUILTIN REWRITE _↦_ #-}  -- currently fails a sanity check

postulate
  resize : ∀{i j} → Set i → Set j
  resize-id : ∀{i} {j} {A : Set i} → resize {i} {j} A ↦ A

{-# REWRITE resize-id #-}

-- Impredicative quantification

Forall : ∀{i} (F : Set i → Set) → Set
Forall {i} F = resize ((X : Set i) → F X)

-- Example: Impredicative encoding of natural numbers

Nat = Forall λ X → (X → X) → X → X

zero : Nat
zero X s z = z

suc : Nat → Nat
suc n X s z = s (n X s z)

-- requires impredicativity:

id : Nat → Nat
id n = n Nat suc zero
