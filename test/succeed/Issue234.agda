-- There was a problem with reordering telescopes.
module Issue234 where

postulate
  A : Set
  P : A → Set

data List : Set where
  _∷ : A → List

data _≅_ {x : A}(p : P x) : ∀ {y} → P y → Set where
  refl : p ≅ p

data _≡_ (x : A) : A → Set where
  refl : x ≡ x

data Any (x : A) : Set where
  here : P x → Any x

it : ∀ {x : A} → Any x → A
it {x} (here _) = x

prf : ∀ {x : A}(p : Any x) → P (it p)
prf (here px) = px

foo : (x : A) (p : Any x) →
      (f : ∀ {y} → it p ≡ y → P y) →
      f refl ≅ prf p →
      Set₁
foo x (here ._) f refl = Set
