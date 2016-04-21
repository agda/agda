
-- {-# OPTIONS -v tc.proj.amb:30 #-}

import Common.Level
open import Common.Prelude hiding (map)
open import Common.Equality

record Stream (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Stream A
open module S = Stream

-- This is a bit trickier for overloading projections
-- as it has a parameter with is of a record type
-- with the same projections.

record _≈_ {A : Set}(s t : Stream A) : Set where
  coinductive
  field
    head : head s ≡ head t
    tail : tail s ≈ tail t
open module B = _≈_

≈refl : ∀{A} {s : Stream A} → s ≈ s
_≈_.head ≈refl = refl
_≈_.tail ≈refl = ≈refl

≈sym : ∀{A} {s t : Stream A} → s ≈ t → t ≈ s
_≈_.head (≈sym p) = sym (head p)
_≈_.tail (≈sym p) = ≈sym (tail p)


map : {A B : Set} → (A → B) → Stream A → Stream B
S.head (map f s) = f (head s)
S.tail (map f s) = map f (tail s)

map_id : {A : Set}(s : Stream A) → map (λ x → x) s ≈ s
B.head (map_id s) = refl
B.tail (map_id s) = map_id (tail s)

repeat : {A : Set}(a : A) → Stream A
S.head (repeat a) = a
S.tail (repeat a) = repeat a

repeat₂ : {A : Set}(a₁ a₂ : A) → Stream A
(       (S.head (repeat₂ a₁ a₂))) = a₁
(S.head (S.tail (repeat₂ a₁ a₂))) = a₂
(S.tail (S.tail (repeat₂ a₁ a₂))) = repeat₂ a₁ a₂

repeat≈repeat₂ : {A : Set}(a : A) → repeat a ≈ repeat₂ a a
(       (B.head (repeat≈repeat₂ a))) = refl
(B.head (B.tail (repeat≈repeat₂ a))) = refl
(B.tail (B.tail (repeat≈repeat₂ a))) = repeat≈repeat₂ a
