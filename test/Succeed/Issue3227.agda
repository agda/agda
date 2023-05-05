-- {-# OPTIONS -v tc.check.term.con:80 #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

variable
  n m : Nat
  A : Set
  x y : A

data Fin : Nat → Set where
  zero : Fin (suc n)
  suc  : Fin n → Fin (suc n)

suc-inj : ∀{n m : Nat} →  suc n ≡ suc m → n ≡ m
suc-inj refl = refl

suc-inj' : suc n ≡ suc m → n ≡ m
suc-inj' refl = refl

postulate
  nn : Nat
  magic : {A : Set} → A → Nat

test = magic (suc nn)

data Vec A : Nat → Set where
  []  : Vec A zero
  _∷_ : A → Vec A n → Vec A (suc n)

data List A : Set where
  [] : List A
  _∷_ : A → List A → List A

variable
  xs ys : List A

cons-inj₁ : (x ∷ xs) ≡ (y ∷ ys) → x ≡ y
cons-inj₁ refl = refl

cons-inj₂ : (x ∷ xs) ≡ (y ∷ ys) → xs ≡ ys
cons-inj₂ refl = refl

cons-inj₁' : ∀{xs ys : List A} → (x ∷ xs) ≡ (y ∷ ys) → x ≡ y
cons-inj₁' refl = refl

vcons-inj₁' : ∀{xs ys : Vec A n} → (x ∷ xs) ≡ (y ∷ ys) → x ≡ y
vcons-inj₁' refl = refl

module M (A : Set) where

  data D : Set where
    c : A → D

open M Nat  renaming (D to DNat)
open M Bool renaming (D to DBool)

inj-c : _≡_ {A = _} (c n) (c m) → n ≡ m
inj-c refl = refl

{-
-- These still fail and we do not intend to fix them:

deep = magic (suc (suc nn))


suc-suc-inj : ∀{n m : Nat} →  suc (suc n) ≡ suc (suc m) → n ≡ m
suc-suc-inj refl = refl


{-
F : Nat → Set
F zero = Nat
F (suc n) = Fin n
-}

-- -}
-- -}
-- -}
-- -}
-- -}
