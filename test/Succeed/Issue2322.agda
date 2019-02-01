{-# OPTIONS --guardedness #-}

open import Agda.Builtin.Coinduction
open import Agda.Builtin.Equality

record Reveal_·_is_ {A : Set} {B : A → Set}
                    (f : (x : A) → B x) (x : A) (y : B x) :
                    Set where
  constructor [_]
  field eq : f x ≡ y

inspect : {A : Set} {B : A → Set}
          (f : (x : A) → B x) (x : A) → Reveal f · x is f x
inspect f x = [ refl ]

infixr 5 _∷_

data Stream (A : Set) : Set where
  _∷_ : (x : A) (xs : ∞ (Stream A)) → Stream A

infix 4 _≈_

data _≈_ {A} : Stream A → Stream A → Set where
  _∷_ : ∀ {x y xs ys}
        (x≡ : x ≡ y) (xs≈ : ∞ (♭ xs ≈ ♭ ys)) → x ∷ xs ≈ y ∷ ys

map : ∀ {A B} → (A → B) → Stream A → Stream B
map f (x ∷ xs) = f x ∷ ♯ map f (♭ xs)

map₂ : ∀ {A B} → (A → B) → Stream A → Stream B
map₂ f (x ∷ xs) with ♭ xs
map₂ f (x ∷ xs) | y ∷ ys = f x ∷ ♯ (f y ∷ ♯ map₂ f (♭ ys))

map≈map₂ : ∀ {A B} →
           (f : A → B) → (xs : Stream A) → map f xs ≈ map₂ f xs
map≈map₂ {A} f (x ∷ xs) with ♭ xs | inspect ♭ xs
map≈map₂ {A} f (x ∷ xs) | y ∷ ys | [ eq ] = refl ∷ ♯ helper eq
  where
  map-f-y∷ys = _

  helper : ∀ {xs} → xs ≡ y ∷ ys → map f xs ≈ map-f-y∷ys
  helper refl = refl ∷ ♯ map≈map₂ f (♭ ys)
