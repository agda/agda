-- {-# OPTIONS --show-implicit #-}

module Issue89 where

open import Common.Coinduction renaming (∞ to ∞_)

------------------------------------------------------------------------
-- Streams

infixr 5 _≺_

data Stream A : Set where
  _≺_ : (x : A) (xs : ∞ (Stream A)) -> Stream A

head : forall {A} -> Stream A -> A
head (x ≺ xs) = x

tail : forall {A} -> Stream A -> Stream A
tail (x ≺ xs) = ♭ xs

------------------------------------------------------------------------
-- Stream programs

infix  8 _∞
infixr 5 _⋎_
infix  4 ↓_

mutual

  data Stream′ A : Set1 where
    _≺_ : (x : A) (xs : ∞ (StreamProg A)) -> Stream′ A

  data StreamProg (A : Set) : Set1 where
    ↓_  : (xs : Stream′ A) -> StreamProg A
    _∞  : (x : A) -> StreamProg A
    _⋎_ : (xs ys : StreamProg A) -> StreamProg A

head′ : ∀ {A} → Stream′ A → A
head′ (x ≺ xs) = x

tail′ : ∀ {A} → Stream′ A → StreamProg A
tail′ (x ≺ xs) = ♭ xs

P⇒′ : forall {A} -> StreamProg A -> Stream′ A
P⇒′ (↓ xs)    = xs
P⇒′ (x ∞)     = x ≺ ♯ (x ∞)
P⇒′ (xs ⋎ ys) with P⇒′ xs
P⇒′ (xs ⋎ ys) | xs′ = head′ xs′ ≺ ♯ (ys ⋎ tail′ xs′)

mutual

  ′⇒ : forall {A} -> Stream′ A -> Stream A
  ′⇒ (x ≺ xs) = x ≺ ♯ P⇒ (♭ xs)

  P⇒ : forall {A} -> StreamProg A -> Stream A
  P⇒ xs = ′⇒ (P⇒′ xs)

------------------------------------------------------------------------
-- Stream equality

infix 4 _≡_ _≈_ _≊_

data _≡_ {a : Set} (x : a) : a -> Set where
  ≡-refl : x ≡ x

data _≈_ {A} (xs ys : Stream A) : Set where
  _≺_ : (x≡ : head xs ≡ head ys) (xs≈ : ∞ (tail xs ≈ tail ys)) ->
        xs ≈ ys

_≊_ : forall {A} (xs ys : StreamProg A) -> Set
xs ≊ ys = P⇒ xs ≈ P⇒ ys

foo : forall {A} (x : A) -> x ∞ ⋎ x ∞ ≊ x ∞
foo x = ≡-refl ≺ ♯ foo x

-- The first goal has goal type
--   head (′⇒ (x ≺ x ∞ ⋎ x ∞)) ≡ head (′⇒ (x ≺ x ∞)).
-- The normal form of the left-hand side is x, and the normal form of
-- the right-hand side is x (both according to Agda), but ≡-refl is
-- not accepted by the type checker:
--   x != head (′⇒ (P⇒′ (x ∞))) of type .A
--   when checking that the expression ≡-refl has type
--   (head (P⇒ (x ∞ ⋎ x ∞)) ≡ head (P⇒ (x ∞)))

