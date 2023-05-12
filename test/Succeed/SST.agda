-- Construction of the four functions SST, SK, SK⃗, and αₖ from
-- "Extending Homotopy Type Theory with Strict Equality" by Thorsten
-- Altenkirch, Paolo Capriotti, Nicolai Kraus (2016)
-- (https://arxiv.org/abs/1604.03799).

{-# OPTIONS --cubical-compatible --two-level --rewriting #-}

open import Agda.Primitive
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma

variable
  ℓ ℓ′ ℓ₁ ℓ₂ ℓ₃ : Level
  A B C : Set ℓ
  x y z : A

infix 4 _≡ₛ_ _≡ₛₛ_
data _≡ₛ_ {A : Set ℓ} (x : A) : A → SSet ℓ where
  instance
    refl : x ≡ₛ x

data _≡ₛₛ_ {A : SSet ℓ} (x : A) : A → SSet ℓ where
  instance
    refl : x ≡ₛₛ x

UIPₛ : {A : Set ℓ} {x y : A} {e₁ e₂ : x ≡ₛ y} → e₁ ≡ₛₛ e₂
UIPₛ {e₁ = refl} {e₂ = refl} = refl

{-# BUILTIN REWRITE _≡ₛₛ_ #-}

sym : x ≡ₛ y → y ≡ₛ x
sym refl = refl

trans : x ≡ₛ y → y ≡ₛ z → x ≡ₛ z
trans refl refl = refl

infixr 10 _≡⟨_⟩ₛ_
_≡⟨_⟩ₛ_ : {A : Set ℓ} (x : A) {y z : A} → x ≡ₛ y → y ≡ₛ z → x ≡ₛ z
x ≡⟨ refl ⟩ₛ refl = refl

infix 15 _∎ₛ
_∎ₛ : {A : Set ℓ} (x : A) → x ≡ₛ x
x ∎ₛ = refl

transport : {A : Set ℓ} (P : A → Set ℓ′) {x y : A} → x ≡ₛ y → P x → P y
transport P refl p = p

transport-merge : {A : Set ℓ} {P : A → Set ℓ′} {x y z : A}
                  {e₁ : x ≡ₛ y} {e₂ : y ≡ₛ z} {p : P x}
                → transport P e₂ (transport P e₁ p) ≡ₛ transport P (trans e₁ e₂) p
transport-merge {e₁ = refl} {e₂ = refl} = refl

transport-pi : {A : Set ℓ₁} {B : Set ℓ₂} {C : A → B → Set ℓ₃}
             → {x₁ x₂ : A} {e : x₁ ≡ₛ x₂} {f : (y : B) → C x₁ y} {y : B}
             → transport (λ x → (y : B) → C x y) e f y ≡ₛ transport (λ x → C x y) e (f y)
transport-pi {e = refl} = refl

cong : (f : A → B) {x₁ x₂ : A} → x₁ ≡ₛ x₂ → f x₁ ≡ₛ f x₂
cong f refl = refl

cong₂ : {A : Set ℓ} {B : A → Set ℓ′} (f : (x : A) → B x → C)
      → {x₁ x₂ : A} {y₁ : B x₁} {y₂ : B x₂}
      → (p : x₁ ≡ₛ x₂) (q : transport B p y₁ ≡ₛ y₂)
      → f x₁ y₁ ≡ₛ f x₂ y₂
cong₂ f refl refl = refl

transport-cong : {f : A → B} {P : B → Set ℓ} {x₁ x₂ : A} {e : x₁ ≡ₛ x₂} {p : P (f x₁)}
               → transport (λ x → P (f x)) e p ≡ₛ transport P (cong f e) p
transport-cong {e = refl} = refl

cong-transport : {A : Set ℓ} {P : A → Set ℓ′} {x y : A} {e₁ e₂ : x ≡ₛ y} {p : P x}
               → e₁ ≡ₛₛ e₂ → transport P e₁ p ≡ₛ transport P e₂ p
cong-transport refl = refl

postulate
  funextₛ : {A : Set ℓ} {B : A → Set ℓ′} {f g : (x : A) → B x}
          → (∀ x → f x ≡ₛ g x) → f ≡ₛ g

data sNat : SSet where
  zero : sNat
  suc  : sNat → sNat

variable
  k l m n : sNat

postulate
  Nat→sNat : Nat → sNat
  zero→szero : Nat→sNat zero ≡ₛₛ zero
  suc→ssuc : ∀ n → Nat→sNat (suc n) ≡ₛₛ suc (Nat→sNat n)

{-# REWRITE zero→szero #-}
{-# REWRITE suc→ssuc #-}

data ⊥ {ℓ} : Set ℓ where

record ⊤ {ℓ} : Set ℓ where
  constructor ∗

data _⊎_ (A B : Set ℓ) : Set ℓ where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

{-# NO_UNIVERSE_CHECK #-}
data Fin : sNat → Set where
  fzero : Fin (suc n)
  fsuc  : Fin n → Fin (suc n)

{-# NO_UNIVERSE_CHECK #-}
data _<ⁿ_ : Fin n → Fin n → Set where
  z<s : fzero <ⁿ fsuc x
  s<s : x <ⁿ y → fsuc x <ⁿ fsuc y

isIncr : (Fin k → Fin l) → Set
isIncr f = ∀ {x} {y} → x <ⁿ y → f x <ⁿ f y

Δ₊ : (i j : sNat) → Set
Δ₊ i j = Σ (Fin i → Fin j) isIncr

_∘_ : Δ₊ l m → Δ₊ k l → Δ₊ k m
(f , f-incr) ∘ (g , g-incr) = (λ x → f (g x)) , λ p → f-incr (g-incr p)

∘-assoc : ∀ {k l m n} {f : Δ₊ k l} {g : Δ₊ l m} {h : Δ₊ m n}
        → (h ∘ g) ∘ f ≡ₛ h ∘ (g ∘ f)
∘-assoc = refl

SST : sNat → Set₁
SK : (k : sNat) → SST k → sNat → Set
SK⃗ : (k : sNat) (X : SST k) {m n : sNat} (f : Δ₊ m n) → SK k X n → SK k X m
α : (k : sNat) {l m n : sNat} (X : SST k) (f : Δ₊ l m) (g : Δ₊ m n)
  → (x : SK k X n) → SK⃗ k X (g ∘ f) x ≡ₛ SK⃗ k X f (SK⃗ k X g x)

SST zero = ⊤
SST (suc k) = Σ (SST k) λ X → (SK k X (suc k) → Set)

SK zero X n = ⊤
SK (suc k) (X , Y) n = Σ (SK k X n) λ x → (f : Δ₊ (suc k) n) → Y (SK⃗ k X f x)

SK⃗ zero X f = λ x → x
SK⃗ (suc k) (X , Y) f (x , h) = SK⃗ k X f x , λ g →
  let h[f∘g] : Y (SK⃗ k X (f ∘ g) x)
      h[f∘g] = h (f ∘ g)
      αₖ : SK⃗ k X (f ∘ g) x ≡ₛ SK⃗ k X g (SK⃗ k X f x)
      αₖ = α k X g f x
  in transport Y αₖ h[f∘g]

α zero X f g x    = refl
α (suc k) {l} {m} {n} (X , Y) f g (x , y) =
  cong₂ _,_ (α k X f g x) (funextₛ λ h →

    transport (λ z → (f′ : Δ₊ (suc k) l) → Y (SK⃗ k X f′ z)) (α k X f g x)
      (λ g′ → transport Y (α k X g′ (g ∘ f) x) (y ((g ∘ f) ∘ g′))) h

      ≡⟨ transport-pi {B = Δ₊ (suc k) l} {C = λ z f′ → Y (SK⃗ k X f′ z)} {e = α k X f g x} ⟩ₛ

    transport (λ z → Y (SK⃗ k X h z)) (α k X f g x)
      (transport Y (α k X h (g ∘ f) x) (y ((g ∘ f) ∘ h)))

      ≡⟨ transport-cong {f = SK⃗ k X h} {P = Y} {e = α k X f g x} ⟩ₛ

    transport Y (cong (SK⃗ k X h) (α k X f g x))
      (transport Y (α k X h (g ∘ f) x) (y ((g ∘ f) ∘ h)))

      ≡⟨ transport-merge {P = Y} {e₂ = cong (SK⃗ k X h) (α k X f g x)} {p = y ((g ∘ f) ∘ h)} ⟩ₛ

    transport Y (trans (α k X h (g ∘ f) x) (cong (SK⃗ k X h) (α k X f g x))) (y ((g ∘ f) ∘ h))

      ≡⟨ cong-transport {P = Y}
           {e₁ = trans (α k X h (g ∘ f) x) (cong (SK⃗ k X h) (α k X f g x))}
           {e₂ = trans (α k X (f ∘ h) g x) (α k X h f (SK⃗ k X g x))}
           {p = y (g ∘ (f ∘ h))} UIPₛ ⟩ₛ

    transport Y (trans (α k X (f ∘ h) g x) (α k X h f (SK⃗ k X g x))) (y (g ∘ (f ∘ h)))

      ≡⟨ sym (transport-merge {e₁ = α k X (f ∘ h) g x} {e₂ = α k X h f (SK⃗ k X g x)} {p = y (g ∘ (f ∘ h))}) ⟩ₛ

    transport Y (α k X h f (SK⃗ k X g x)) (transport Y (α k X (f ∘ h) g x) (y (g ∘ (f ∘ h))))
      ∎ₛ

  )
