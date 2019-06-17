{-# OPTIONS --prop --rewriting --confluence-check #-}

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Nat renaming (Nat to ℕ; _+_ to _+ℕ_)

infix 4 _≐_
data _≐_ {ℓ} {A : Set ℓ} (x : A) : A → Prop ℓ where
  refl : x ≐ x

{-# BUILTIN REWRITE _≐_ #-}

variable
  ℓ : Level
  A B C : Set ℓ
  x y z : A

cong : (f : A → B) → x ≐ y → f x ≐ f y
cong f refl = refl

data ℤ : Set where
  zero : ℤ
  pred suc : ℤ → ℤ

postulate
  pred-suc : (x : ℤ) → pred (suc x) ≐ x
  suc-pred : (x : ℤ) → suc (pred x) ≐ x

{-# REWRITE pred-suc suc-pred #-}

count-suc : ℤ → ℕ
count-suc zero = 0
count-suc (pred x) = count-suc x
count-suc (suc x) = 1 +ℕ count-suc x
