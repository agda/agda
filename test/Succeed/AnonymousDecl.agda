module AnonymousDecl where

_ : Set₁
_ = Set

_ : Set → Set
_ = λ x → x

_∋_ : ∀ {ℓ} (A : Set ℓ) → A → A
A ∋ a = a

_ = Set₁
_ = (Set → Set) ∋ λ x → x

data Bool : Set where t f : Bool

not : Bool → Bool
not t = f
not f = t

data _≡_ {A : Set} (a : A) : A → Set where
  refl : a ≡ a

_ : ∀ x → not (not x) ≡ x
_ = λ { t → refl; f → refl }
