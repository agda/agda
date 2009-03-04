
module InferrableFields where

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

data Vec A : ℕ → Set where
  []  : Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

record SomeVec A : Set where
  field n      : ℕ
        unpack : Vec A n

open SomeVec using (unpack)

pack : ∀ {A n} → Vec A n -> SomeVec A
pack xs = record { unpack = xs }

data _≡_ {A : Set}(x : A) : A → Set where
  refl : x ≡ x

lemPack : ∀ {A}(xs : SomeVec A) → pack (unpack xs) ≡ xs
lemPack xs = refl