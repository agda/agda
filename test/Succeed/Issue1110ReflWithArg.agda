-- Andreas, 2014-05-17 reported by Fabien Renaud
-- Rewriting with refl-proof.
-- Andreas, 2017-01-11 test extended for other definition of REFL.

{-# OPTIONS --allow-unsolved-metas #-}

data _≡_ {a} {A : Set a} : (x y : A) → Set a where
  refl : ∀{x} → x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

{-# BUILTIN NATURAL Nat #-}

data List {a} (A : Set a) : Set a where
  [] : List A
  _∷_ : A → List A → List A

length : ∀{a}{A : Set a} → List A → Nat
length [] = zero
length (x ∷ xs) = suc (length xs)

foldr : ∀{a b}{A : Set a}{B : Set b} → (A → B → B) → B → List A → B
foldr c n [] = n
foldr c n (x ∷ xs) = c x (foldr c n xs)

length-cons : ∀{b} {B : Set b} (L : List B) x → length (x ∷ L) ≡ suc (length L)
length-cons []      _ = refl
length-cons (x ∷ L) _ = refl

suc-foldr-eq : ∀{b} {c} {B : Set b} {C : Set c} (LL : List B) (LA : List C)

  → suc (foldr (λ _ → suc) 0 LL) ≡
    suc (foldr (λ _ → suc) 0 LA)

  → length LL ≡
    length LA

suc-foldr-eq [] [] Eq = refl
suc-foldr-eq [] (x ∷ LA) ()
suc-foldr-eq (x ∷ LL) [] ()
suc-foldr-eq (x ∷ LL) (y ∷ LA) Eq rewrite length-cons LL x = {!!}

-- WAS:
-- Failed to infer the value of dotted pattern
-- when checking that the pattern ._ has type Nat

-- NOW: unsolved meta
