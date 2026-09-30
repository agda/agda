module Auto.Prelude where

open import Agda.Primitive        public using (Level)
open import Agda.Builtin.Equality public


data ⊥ : Set where

¬ : Set → Set
¬ A = A → ⊥

⊥-e : (A : Set) → ⊥ → A
⊥-e A ()


record ⊤ : Set where



record _∧_ (A B : Set) : Set where
 constructor ∧-i
 field fst : A
       snd : B

data _∨_ (A B : Set) : Set where
 ∨-i₁ : A → A ∨ B
 ∨-i₂ : B → A ∨ B

∨-e : (A B C : Set) → A ∨ B → (A → C) → (B → C) → C
∨-e A B C (∨-i₁ x) h₁ h₂ = h₁ x
∨-e A B C (∨-i₂ x) h₁ h₂ = h₂ x


data Π (A : Set) (F : A → Set) : Set where
  fun : ((a : A) → F a) → Π A F

record Σ (X : Set) (P : X → Set) : Set where
 constructor Σ-i
 field wit : X
       prf : P wit


data ℕ : Set where
 zero : ℕ
 succ : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero   + n = n
succ m + n = succ (m + n)


data Fin : ℕ → Set where
  zero : ∀ {n} → Fin (succ n)
  suc  : ∀ {n} → Fin n → Fin (succ n)


data List (X : Set) : Set where
  []  : List X
  _∷_ : X → List X → List X

_++_ : {X : Set} → List X → List X → List X
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)


data Vec (X : Set) : ℕ → Set where
  []  : Vec X zero
  _∷_ : ∀ {n} → X → Vec X n → Vec X (succ n)

-- -----------------------------------

subst : {i j : Level} {X : Set i} → (P : X → Set j) → (x y : X) → y ≡ x → P x → P y
subst P x .x refl h = h

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

-- -----------------------------------
