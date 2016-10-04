
data ⊥ : Set where

data Bool : Set where
  false true : Bool

data _≡_ (x : Bool) : Bool → Set where
  refl : x ≡ x

true≠false : false ≡ true → ⊥
true≠false ()

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A → Maybe A

data Eq {A : Set} (_≈_ : A → A → Set) : Maybe A → Maybe A → Set where
  just    : ∀ {x y} (x≈y : x ≈ y) → Eq _≈_ (just x) (just y)
  nothing : Eq _≈_ nothing nothing

drop-just : ∀ {A : Set} {_≈_ : A → A → Set} {x y : A} →
            Eq _≈_ (just x) (just y) → x ≈ y
drop-just (just x≈y) = x≈y
