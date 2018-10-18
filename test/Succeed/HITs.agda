{-# OPTIONS --cubical #-}
open import Agda.Builtin.Cubical.Path

data PushOut {A B C : Set} (f : C → A) (g : C → B) : Set where
  inl : A → PushOut f g
  inr : B → PushOut f g
  push : ∀ c → inl (f c) ≡ inr (g c)
  squash : ∀ a b → a ≡ b

data ∥_∥₀ (A : Set) : Set where
  ∣_∣    : A → ∥ A ∥₀
  squash : ∀ (x y : ∥ A ∥₀) → (p q : x ≡ y) → p ≡ q

data Segment : Set where
  start end : Segment
  line      : start ≡ end

-- prop truncation
data ∥_∥ (A : Set) : Set where
  ∣_∣ : A → ∥ A ∥
  squash : ∀ (x y : ∥ A ∥) → x ≡ y

elim : ∀ {A : Set} (P : Set) → ((x y : P) → x ≡ y) → (A → P) → ∥ A ∥ → P
elim P Pprop f ∣ x ∣          = f x
elim P Pprop f (squash x y i) = Pprop (elim P Pprop f x) (elim P Pprop f y) i
