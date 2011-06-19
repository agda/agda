{-# OPTIONS --universe-polymorphism #-}

module AutoMisc where

-- prelude

postulate
  Level : Set
  lzero : Level
  lsuc  : (i : Level) → Level

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO lzero  #-}
{-# BUILTIN LEVELSUC  lsuc   #-}

data _≡_ {a} {A : Set a} (x : A) : A → Set where
  refl : x ≡ x

trans : ∀ {a} {A : Set a} → {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

sym : ∀ {a} {A : Set a} → {x y : A} → x ≡ y → y ≡ x
sym refl = refl

cong : ∀ {a b} {A : Set a} {B : Set b}
       (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

data _IsRelatedTo_ {a : Level} {Carrier : Set a} (x y : Carrier) : Set a where
  relTo : (x∼y : x ≡ y) → x IsRelatedTo y

begin_ : {a : Level} {Carrier : Set a} → {x y : Carrier} → x IsRelatedTo y → x ≡ y
begin relTo x∼y = x∼y

_∎ : {a : Level} {Carrier : Set a} → (x : Carrier) → x IsRelatedTo x
_∎ _ = relTo refl

_≡⟨_⟩_ : {a : Level} {Carrier : Set a} → (x : Carrier) {y z : Carrier} → x ≡ y → y IsRelatedTo z → x IsRelatedTo z
_ ≡⟨ x∼y ⟩ relTo y∼z = relTo (trans x∼y y∼z)

data ℕ : Set where
  zero : ℕ
  suc  : (n : ℕ) → ℕ

_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)

data ⊥ : Set where

¬ : Set → Set
¬ A = A → ⊥

data Π (A : Set) (F : A → Set) : Set where
  fun : ((a : A) → F a) → Π A F

data Σ (A : Set) (F : A → Set) : Set where
  ΣI : (a : A) → (F a) → Σ A F

data Fin : ℕ → Set where
  zero : ∀ {n} → Fin (suc n)
  suc  : ∀ {n} → Fin n → Fin (suc n)

data List (X : Set) : Set where
  []  : List X
  _∷_ : X → List X → List X

_++_ : {X : Set} → List X → List X → List X
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

data Vec (X : Set) : ℕ → Set where
  []  : Vec X zero
  _∷_ : ∀ {n} → X → Vec X n → Vec X (suc n)


module AdditionCommutative where

 lemma : ∀ n m → (n + suc m) ≡ suc (n + m)
 lemma n m = {!!}

 lemma' : ∀ n m → (n + suc m) ≡ suc (n + m)
 lemma' zero m = refl
 lemma' (suc n) m = cong suc (lemma' n m)

 addcommut : ∀ n m → (n + m) ≡ (m + n)
 addcommut n m = {!!}


module Drink where

 postulate RAA : (A : Set) → (¬ A → ⊥) → A

 drink : (A : Set) → (a : A)
            → (Drink : A → Set) → Σ A (λ x → (Drink x) → Π A Drink)
 drink A a Drink = {!!}


module VecMap where

 map : {X Y : Set} → {n : ℕ} → (X → Y) → Vec X n → Vec Y n
 map f xs = {!!} 


module Disproving where

 p : {X : Set} → (xs ys : List X) → (xs ++ ys) ≡ (ys ++ xs)
 p = {!!}
